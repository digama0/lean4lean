import Lean4Lean.Theory.Typing.Confluence.SingletonRecursorExtraction
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaCoverage
import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Inductive.InstanceSpecialize
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.SingletonExtraction.TelescopeTyping
import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.SignatureVars
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.CanonicalEq
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.Confluence.SingletonRecursorTyping
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.NormalSubstitution
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.PrefixUnfolding.Arity
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.SingletonExtraction.Scope
import Lean4Lean.Theory.Inductive.RecursorPrefixUnfolding
import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule
import Lean4Lean.Theory.Typing.LevelledReduction
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.SingletonExtraction.RecursorScope
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Std.List
import Lean4Lean.Theory.Inductive.CompilationLemmas

/-! # Coverage of zero-source singleton recursor equations

At a universe specialization where the source of a large-eliminating
recursor is `Prop`, its installed equation is joined by the singleton
prefix unfolding at the recursor's prefix (all arguments before the
constructor major), a beta step with the constructor major, and proof
irrelevance for the reconstructed proof fields. The replay of the singleton
program at this literal instance is typed by the `Eq`-cast extraction
(`SingletonExtraction.lean`), which needs canonical `Eq`. -/

namespace Lean4Lean.InductiveSignature
open VExpr VEnv CaseSchema RecursorData
set_option backward.isDefEq.respectTransparency false

private theorem extract_wrap_const {lhs rhs type : VExpr}
    {name : Name} {levels : List VLevel}
    (hhead : lhs.getAppFnArgs.1 = .const name levels) (domains : List VExpr) :
    EquationBody.extract (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains type) = some ⟨domains, lhs, rhs, type⟩ := by
  induction domains with
  | nil => cases lhs <;> first | rfl | cases hhead
  | cons domain domains ih =>
    change (do
      if domain ≠ domain ∨ domain ≠ domain then none else
      let body ← EquationBody.extract (wrapLams domains lhs) (wrapLams domains rhs)
        (wrapForalls domains type)
      pure { body with domains := domain :: body.domains }) = _
    simp [ih]

end Lean4Lean.InductiveSignature

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv

variable {env : VEnv} {data : RecursorData} {ls : List VLevel}

/-- The explicit extraction data of a registered singleton recursor at an
occurrence where its source is `Prop`. -/
theorem singleton_shape (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner) :
    ∃ k, data.target = .param k ∧
      data.schema.signature.families.size = 1 ∧ data.schema.signature.constructors.size = 1 ∧
      data.schema.restoration = {} ∧
      data.singletonLayout env ls = some ((data.recursorInstance.specialize 0 (ls.set k .zero)).singletonCast
        data.owner data.schema.signature.constructors[index]
        ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))) ∧
      data.propElim ls = some ((data.recursorInstance.specialize 0 (ls.set k .zero)).singletonElim
        data.owner data.schema.signature.constructors[index] (.const data.name (ls.set k .zero))) ∧
      data.propParams ls = (data.recursorInstance.specialize 0 (ls.set k .zero)).params ∧
      (data.recursorInstance.specialize 0 (ls.set k .zero)).levels = data.levels.map (·.inst ls) ∧
      data.singletonEquation = data.equation index := by
  have F := singletonSignature H hlarge hzero
  obtain ⟨k, hk, hkU, hfree⟩ := F.free
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := index.isLt; omega
  have hfam := F.families
  have htp : data.targetParam = some k := by simp [targetParam, hk]
  have hsc : data.singletonCtor = some index := by
    unfold singletonCtor
    have hfr : List.finRange data.schema.signature.constructors.size = [index] := by
      apply List.ext_getElem (by simp [hcs])
      intro n h1 h2
      simp only [List.length_finRange, hcs] at h1
      simp only [List.getElem_finRange, List.getElem_singleton]
      ext; simp; omega
    rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using howner), List.filter_nil]
  have hlev : data.levels.map (·.inst (ls.set k .zero)) = data.levels.map (·.inst ls) :=
    List.map_congr_left fun l hl => hfree l hl ls .zero
  let gp := data.recursorInstance.specialize 0 (ls.set k .zero)
  have hgpl : gp.levels = data.levels.map (·.inst ls) := hlev
  refine ⟨k, hk, hfam, hcs, F.restoration, ?_, ?_, ?_, hgpl, ?_⟩
  · have hFeq : (data.recursorInstance.fieldsAt data.schema.signature.constructors[index]).map
        (·.instL ls) = gp.fieldsAt data.schema.signature.constructors[index] := by
      simp [gp, Instance.fieldsAt, Instance.specialize, recursorInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hIeq : (data.recursorInstance.indicesAt data.owner).map (·.instL ls) =
        gp.indicesAt data.owner := by
      simp [gp, Instance.indicesAt, Instance.specialize, recursorInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hCIeq : (data.recursorInstance.ctorIndicesAt data.schema.signature.constructors[index]).map
        (·.instL ls) = gp.ctorIndicesAt data.schema.signature.constructors[index] := by
      simp [gp, Instance.ctorIndicesAt, Instance.specialize, recursorInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    simp only [singletonLayout, singletonLayoutGeneric, hsc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.map_some]
    simp only [SingletonLayout.instL, Instance.singletonCast, Option.some.injEq, SingletonLayout.mk.injEq]
    refine ⟨hFeq, hIeq, ?_, trivial⟩
    rw [← hFeq, ← hCIeq, List.length_map]
    congr 1; funext j; exact (fieldSlot_instL _ _ _ _).symm
  · simp only [propElim, htp, hsc, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · simp [propParams, Instance.params, Instance.specialize, recursorInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  · unfold singletonEquation RecursorData.equation
    have hfr : (List.finRange data.schema.signature.constructors.size).filter
        (fun i => data.schema.signature.constructors[i].owner == data.owner) = [index] := by
      have hfr : List.finRange data.schema.signature.constructors.size = [index] := by
        apply List.ext_getElem (by simp [hcs])
        intro n h1 h2
        simp only [List.length_finRange, hcs] at h1
        simp only [List.getElem_finRange, List.getElem_singleton]
        ext; simp; omega
      rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using howner), List.filter_nil]
    simp only [hfr]

/-- The syntax of the installed equation of a registered singleton recursor,
at a universe specialization where its source is `Prop`, in terms of its
extraction data. -/
theorem singleton_equation_syntax (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    (hlen : ls.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    {S : SingletonLayout} {E : PropElim}
    (hS : data.singletonLayout env ls = some S) (hE : data.propElim ls = some E) :
    ∃ D lb rb tb X, data.equation index = some ⟨data.uvars, wrapLams D lb, wrapLams D rb,
        wrapForalls D tb⟩ ∧
      data.singletonEquation = data.equation index ∧
      CaseSchema.EquationBody.extract (wrapLams D lb) (wrapLams D rb) (wrapForalls D tb) =
        some ⟨D, lb, rb, tb⟩ ∧
      D.map (·.instL ls) = data.propParams ls ++ X ++ insertBinders S.fields 2 ∧ X.length = 2 ∧
      lb.instL ls = .app
        (mkApps (.const data.name ls) (vars data.indexOffset S.fields.length ++
          E.ctorIndices.map (·.liftN 2 S.fields.length)))
        (mkApps E.ctor (vars (data.propParams ls).length (2 + S.fields.length) ++
          vars S.fields.length 0)) ∧
      data.indexOffset = (data.propParams ls).length + 2 ∧
      data.recursorType = some (data.recursorInstance.recursorType data.owner) := by
  obtain ⟨k, hk, hfam, hcs, hres, hS0, hE0, hP, hgl, hseq⟩ :=
    singleton_shape H hlarge hzero howner
  rw [hS0] at hS; cases Option.some.inj hS
  rw [hE0] at hE; cases Option.some.inj hE
  have F := singletonSignature H hlarge hzero
  let s := data.schema.signature
  let c := s.constructors[index]
  let g := data.recursorInstance
  have hextra : s.families.size + s.constructors.size = 2 := by simp [s, hfam, hcs]
  have hlev : data.levels.map (·.inst (ls.set k .zero)) = data.levels.map (·.inst ls) := hgl
  refine ⟨g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes c).map (·.instL g.levels)) (s.families.size + s.constructors.size),
    mkApps (g.recursorHead .recursor c.owner)
      (vars (s.params.length + (s.families.size + s.constructors.size)) c.fields.length ++
        c.indices.map (fun e => (e.instL g.levels).liftN (s.families.size + s.constructors.size)
          c.fields.length) ++
        [g.constructorApp c (s.families.size + s.constructors.size) 0]),
    ?rb, ?tb, (g.motives ++ g.minors).map (·.instL ls), ?h1, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7, ?h8⟩
  case h1 =>
    unfold RecursorData.equation
    rw [hres, Restoration.equation_empty]
    rfl
  case h2 => exact hseq
  case h3 => exact extract_wrap_const (by exact VExpr.getAppFnArgs_mkApps_head _ _) _
  case h4 =>
    have hpar : g.params.map (·.instL ls) =
        (data.recursorInstance.specialize 0 (ls.set k .zero)).params := by
      simp only [Instance.params, Instance.specialize, g, recursorInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hins : (insertBinders ((s.fieldTypes c).map (·.instL g.levels))
        (s.families.size + s.constructors.size)).map (·.instL ls) =
        insertBinders ((data.recursorInstance.specialize 0 (ls.set k .zero)).singletonCast data.owner
          data.schema.signature.constructors[index]
          ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))).fields 2 := by
      rw [hextra]
      simp only [insertBinders, Instance.singletonCast, Instance.fieldsAt, List.map_map,
        Function.comp_def, VExpr.instL_liftN, hgl, List.zipIdx_map]
      simp [g, recursorInstance, c, s, VExpr.instL_instL]
    rw [hP]
    simp only [List.map_append, List.append_assoc, hpar, hins]
  case h5 => simp [Instance.motives, Instance.minors, hfam, hcs]
  case h7 =>
    rw [hP]; simp [indexOffset, numParams, Instance.params, Instance.specialize, hfam, hcs]
  case h8 =>
    unfold RecursorData.recursorType
    rw [hres, Restoration.expr_empty]
  case h6 =>
    have hnf : ((data.recursorInstance.specialize 0 (ls.set k .zero)).singletonCast data.owner
        data.schema.signature.constructors[index]
        ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))).fields.length =
        c.fields.length := by
      simp [Instance.singletonCast, Instance.fieldsAt, InductiveSignature.fieldTypes, c, s]
    have hnp : (data.propParams ls).length = s.params.length := by
      rw [hP]; simp [Instance.params, s]
    have hname : g.recursorName c.owner = data.name := by
      have := congrArg (fun o : Fin _ => (data.schema.signature.families[o]).name.str "rec") howner
      simpa [g, recursorInstance, RecursorData.name, hres, Restoration.recursorName, c, s] using this
    have hio : data.indexOffset = s.params.length + (s.families.size + s.constructors.size) := by
      simp [indexOffset, numParams, Nat.add_assoc, s]
    rw [hnf, hnp, hio, hextra]
    simp only [VExpr.mkApps_snoc, VExpr.instL, VExpr.instL_mkApps, List.map_append, Instance.recursorHead,
      hname, VEnv.vars_instL, List.map_map, Function.comp_def, VExpr.instL_liftN, VExpr.instL_instL,
      Instance.constructorApp, Instance.singletonElim, Instance.ctorIndicesAt]
    have hu : (VLevel.params g.uvars).map (VLevel.inst ls) = ls := VLevel.inst_map_id hlen
    have hgl' : (data.recursorInstance.specialize 0 (ls.set k .zero)).levels =
        g.levels.map (VLevel.inst ls) := hgl
    rw [hu, hgl']
    rfl

theorem singleton_slot_lt (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    {S : SingletonLayout} (hS : data.singletonLayout env ls = some S) :
    ∀ l k, S.slot.getD l none = some k → l < S.fields.length := by
  obtain ⟨k, -, -, -, -, hS0, -⟩ := singleton_shape H hlarge hzero howner
  rw [hS0] at hS; cases Option.some.inj hS
  intro l j h
  rw [Instance.singletonCast_slot] at h
  split at h
  · simpa [Instance.singletonCast] using ‹_›
  · cases h

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem instOuter_liftN_skip {X : VExpr} {A B : List VExpr} {P r : Nat}
    (hX : X.ClosedN (P + B.length)) (hA : A.length = P + r) :
    (X.liftN r B.length).instOuter (A ++ B) = X.instOuter (A.take P ++ B) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  have hAt : (A.take P).length = P := by simp; omega
  by_cases hik : i < B.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ (by simp; omega),
      VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_lt _ (by simp; omega),
      VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_take]
    congr 1; simp; omega

theorem TelInst.instOuter_args {env : VEnv} {U : Nat} (henv : env.WF)
    {doms' doms args args' : List VExpr} {Γ : List VExpr}
    (hctx : OnCtx doms'.reverse (env.IsType U))
    (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j)
    (H : TelInst env U doms'.reverse doms args) (H' : TelInst env U Γ doms' args') :
    TelInst env U Γ doms (args.map (·.instOuter args')) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_map] at hj
  have h := HasType.closed_instOuter henv hctx (H.2 j hj hj') H'
  rw [instOuter_instOuter _ _ _ (by simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using hcl j hj')] at h
  simpa [List.map_take] using h

theorem InstForallsC.supplyType_eq {env : VEnv} {U : Nat} {Γ : List VExpr} {T : VExpr}
    {args : List VExpr} {res : VExpr} (H : InstForallsC env U Γ T args res) :
    RecursorData.supplyType args T = some res := by
  induction H with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem instOuter_vars_lift {X : VExpr} {n k : Nat} (hX : X.ClosedN n) :
    X.instOuter (vars n k) = X.liftN k := by
  rw [vars_eq_bvarRange, instOuter_range_bvar' _ _ _ hX (by omega), Nat.add_sub_cancel_left]

theorem vars_add (a b k : Nat) : vars (a + b) k = vars a (b + k) ++ vars b k := by
  apply List.ext_getElem (by simp [vars])
  intro i h1 h2
  simp only [vars, List.length_map, List.length_reverse, List.length_range] at h1
  by_cases hi : i < a
  · rw [List.getElem_append_left (by simp [vars]; omega)]
    simp [vars]; omega
  · rw [List.getElem_append_right (by simp [vars]; omega)]
    simp [vars]; omega

theorem vars_map_inst_succ (n k : Nat) (a : VExpr) :
    (vars n (k + 1)).map (·.inst a) = vars n k := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  simp only [VExpr.inst, VExpr.instVar]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1; omega

theorem vars_map_lift (n k : Nat) : (vars n k).map VExpr.lift = vars n (k + 1) := by
  simpa using InductiveSignature.vars_map_liftN_hi n k 1 0 (Nat.zero_le _)

theorem instOuter_vars_skip {X : VExpr} {np nf r k : Nat} (hX : X.ClosedN (np + nf)) :
    X.instOuter (vars np (r + nf + k) ++ vars nf k) = (X.liftN r nf).liftN k := by
  have hc : (X.liftN r nf).ClosedN (np + r + nf) := by
    have := hX.liftN (n := r) (j := nf); simpa [Nat.add_assoc, Nat.add_comm r nf] using this
  have h1 := instOuter_vars_lift (k := k) hc
  rw [vars_add, vars_add np r] at h1
  have hl : (vars nf k).length = nf := by simp [vars]
  have hsk := instOuter_liftN_skip (X := X) (A := vars np (r + (nf + k)) ++ vars r (nf + k))
    (B := vars nf k) (P := np) (r := r) (by rw [hl]; exact hX) (by simp [vars])
  rw [hl, List.take_left' (by simp [vars])] at hsk
  rw [← h1, hsk]
  congr 3; omega

theorem map_instOuter_vars (n k : Nat) (args : List VExpr) (h : n + k ≤ args.length) :
    (vars n k).map (·.instOuter args) = (args.drop (args.length - (n + k))).take n := by
  rw [vars_eq_bvarRange, instOuter_bvarRange _ _ _ (by omega) h]

section
variable [Params]
open Params

theorem FullReduction.wrapLams' {domains : List VExpr} {body body' : VExpr} {Γ : List VExpr}
    (H : FullReduction (domains.reverse ++ Γ) body body') :
    FullReduction Γ (VExpr.wrapLams domains body) (VExpr.wrapLams domains body') := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons d ds ih =>
    exact FullReduction.lam .rfl (ih (Γ := d :: Γ) (by simpa using H))

end

section Literal
variable {env : VEnv} {U : Nat} {S : SingletonLayout} {P : List VExpr} {E : PropElim}

theorem _root_.Lean4Lean.PropElim.instOuter_branch {ps f : List VExpr}
    (hl : (ps ++ f).length = P.length + S.fields.length) (hpsl : ps.length = P.length) :
    (PropElim.branchPa S P).map (·.instOuter (ps ++ f)) = ps := by
  unfold PropElim.branchPa
  rw [instOuter_bvarRange _ _ _ (by omega) (by omega)]
  simp [hl, List.take_left' hpsl]

/-- At a literal constructor instance, the indices are the constructor's own
indices and the major is the constructor application. -/
theorem _root_.Lean4Lean.PropElim.WF.literal_args (henv : env.WF) (W : E.WF S P env U)
    {Δ ps f : List VExpr} (hpsl : ps.length = P.length)
    (hf : TelInst env U Δ (P ++ S.fields) (ps ++ f)) :
    TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [VExpr.mkApps E.ctor (ps ++ f)]) := by
  have T := W.typed
  have hl : (ps ++ f).length = P.length + S.fields.length := by
    have := hf.1; simpa using this
  have hctx : OnCtx (P ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hclI := T.prefix_closed (rest := S.indices) fun i h => T.scope.indices i h
  have hci := TelInst.instOuter_args henv hctx hclI W.ctorIndices_typed hf
  rw [List.map_append, PropElim.instOuter_branch hl hpsl] at hci
  refine hci.append_one ?_
  have hM := HasType.closed_instOuter henv hctx W.ctor_typed hf
  have hctor : (PropElim.ctorApp S P E).instOuter (ps ++ f) = VExpr.mkApps E.ctor (ps ++ f) := by
    unfold PropElim.ctorApp
    rw [← hl]
    exact instOuter_bvarRange_apps W.ctor_closed _
  rw [hctor] at hM
  have hmaj : (PropElim.majorTy S P E).instOuter (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) =
      VExpr.mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) := by
    unfold PropElim.majorTy
    exact PropElim.mkApps_instOuter_heads W.family_closed _ _ _ _ hpsl
      (by simp [W.ctorIndices_length])
  rw [hmaj]
  simpa only [VExpr.instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append,
    PropElim.instOuter_branch hl hpsl] using hM

theorem TelInst.getD_mid {Γ A B C a b c : List VExpr} (H : TelInst env U Γ (A ++ B ++ C) (a ++ b ++ c))
    (ha : a.length = A.length) (hb : b.length = B.length) {j : Nat} (hj : j < B.length) :
    env.HasType U Γ (b.getD j default) ((B.getD j default).instOuter (a ++ b.take j)) := by
  have h := H.getD (j := A.length + j) (by simp; omega)
  simp only [List.append_assoc] at h
  rw [getD_append_right' (l₁ := a) (by omega), getD_append_right' (l₁ := A) (by omega), ha,
    Nat.add_sub_cancel_left, getD_append_left' (l₁ := b) (by omega),
    getD_append_left' (l₁ := B) (by omega), ← ha, List.take_append,
    List.take_of_length_le (l := a) (by omega), List.take_append, Nat.add_sub_cancel_left,
    show j - b.length = 0 by omega, List.take_zero, List.append_nil] at h
  exact h

theorem _root_.Lean4Lean.PropElim.WF.literal_index (W : E.WF S P env U) {ps f : List VExpr}
    (hl : (ps ++ f).length = P.length + S.fields.length) (hpsl : ps.length = P.length)
    {l k : Nat} (hs : S.slot.getD l none = some k) (hlf : l < S.fields.length) :
    (E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default = f.getD l default := by
  have hk : k < E.ctorIndices.length := by
    rw [W.ctorIndices_length]; exact W.typed.scope.slot_lt l k hs
  have hfl : f.length = S.fields.length := by simp at hl; omega
  rw [getD_of_lt (by simpa using hk), List.getElem_map, ← getD_of_lt hk, W.slot_literal l k hs,
    VExpr.instOuter_bvar _ (by simp; omega), getD_of_lt (by omega)]
  rw [List.getElem_append_right (by simp; omega)]
  congr 1; simp; omega

/-- The singleton reconstruction at a literal constructor instance, for any
major typed at the instance's type. -/
theorem _root_.Lean4Lean.PropElim.WF.literal_occ (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    {Δ ps f : List VExpr} {m : VExpr} (hΔ : OnCtx Δ (env.IsType U))
    (hpsl : ps.length = P.length) (hf : TelInst env U Δ (P ++ S.fields) (ps ++ f))
    (hm : env.HasType U Δ m ((PropElim.majorTy S P E).instOuter
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))))) :
    TelInst env U Δ (P ++ S.fields)
        (ps ++ (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2) ∧
      (∀ l, l < S.fields.length → env.IsDefEq U Δ
        ((PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2.getD l default)
        (f.getD l default)
        ((S.fields.getD l default).instOuter (ps ++
          (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2.take l))) ∧
      env.IsDefEq U Δ m (VExpr.mkApps E.ctor (ps ++
        (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2))
        ((PropElim.majorTy S P E).instOuter (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)))) := by
  have hl : (ps ++ f).length = P.length + S.fields.length := by
    have := hf.1; simpa using this
  have hfl : f.length = S.fields.length := by simp at hl; omega
  have hargs0 := W.literal_args henv hpsl hf
  have hidxl : (E.ctorIndices.map (·.instOuter (ps ++ f))).length = S.indices.length := by
    simp [W.ctorIndices_length]
  have hargs : TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]) := by
    have h1 := hargs0.take
    have hlen : (P ++ S.indices).length =
        (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))).length := by
      simp [hpsl, W.ctorIndices_length]
    rw [hlen, List.take_left] at h1
    exact h1.append_one hm
  have halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Δ (f.getD l default) ((E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)) := by
    intro l k hs
    have hlf := hslot l k hs
    rw [W.literal_index hl hpsl hs hlf]
    exact TelInst.getD_mid (C := []) (c := []) (by simpa using hf) hpsl hfl hlf
  have hidx : ∀ k, k < S.indices.length →
      env.IsDefEq U Δ ((E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default)
        ((E.ctorIndices.getD k default).instOuter (ps ++ f))
        ((S.indices.getD k default).instOuter (ps ++ (E.ctorIndices.map (·.instOuter (ps ++ f))).take k)) := by
    intro k hk
    have h := TelInst.getD_mid hargs0 hpsl hidxl hk
    have he : (E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default =
        (E.ctorIndices.getD k default).instOuter (ps ++ f) := by
      rw [getD_of_lt (by rw [hidxl]; exact hk), getD_of_lt (by rw [W.ctorIndices_length]; exact hk),
        List.getElem_map]
    rw [← he]; exact h
  obtain ⟨_, h2, h3, _⟩ := PropElim.occ_typed P henv heq W hΔ hpsl hargs hf halign
    S.fields.length (Nat.le_refl _)
  rw [List.take_length] at h2
  exact ⟨h2, h3, PropElim.singleton_eta P henv heq W hΔ hpsl hargs hf halign hidx⟩

theorem _root_.Lean4Lean.PropElim.WF.majorTy_instOuter (W : E.WF S P env U) {ps idx : List VExpr}
    (hpsl : ps.length = P.length) (hidx : idx.length = S.indices.length) :
    (PropElim.majorTy S P E).instOuter (ps ++ idx) = VExpr.mkApps E.family (ps ++ idx) := by
  unfold PropElim.majorTy
  exact PropElim.mkApps_instOuter_heads W.family_closed _ _ _ _ hpsl hidx

theorem TelInst.drop_mid {Γ A M B a m b : List VExpr}
    (H : TelInst env U Γ (A ++ M ++ B.mapIdx (fun l d => d.liftN M.length l)) (a ++ m ++ b))
    (ha : a.length = A.length) (hm : m.length = M.length)
    (hcl : ∀ k (h : k < B.length), (B[k]).ClosedN (A.length + k)) :
    TelInst env U Γ (A ++ B) (a ++ b) := by
  have hbl : b.length = B.length := by have := H.1; simp at this; omega
  have HA : TelInst env U Γ A a := by
    have h := (show TelInst env U Γ (A ++ (M ++ B.mapIdx (fun l d => d.liftN M.length l)))
      (a ++ (m ++ b)) by simpa only [List.append_assoc] using H).take
    rwa [← ha, List.take_left] at h
  refine HA.append hbl fun j hj => ?_
  have h := TelInst.getD_mid (A := A ++ M) (a := a ++ m) (B := B.mapIdx (fun l d => d.liftN M.length l))
    (b := b) (C := []) (c := []) (by simpa using H) (by simp [ha, hm])
    (by simp [hbl]) (j := j) (by simpa using hj)
  have hX : (B.getD j default).ClosedN (A.length + j) := by
    rw [getD_of_lt hj]; exact hcl j hj
  have htl : (b.take j).length = j := by simp; omega
  have hsk := instOuter_liftN_skip (X := B.getD j default) (A := a ++ m) (B := b.take j)
    (P := A.length) (r := M.length) (by rw [htl]; exact hX) (by simp [ha, hm])
  rw [htl, List.take_left' ha] at hsk
  rw [getD_of_lt (l := B.mapIdx (fun l d => d.liftN M.length l)) (by simpa using hj),
    List.getElem_mapIdx, ← getD_of_lt hj, hsk] at h
  exact h

theorem _root_.Lean4Lean.PropElim.occ_getD_prefix (ps idx : List VExpr) (m : VExpr) {l : Nat} :
    ∀ n, l < n → (PropElim.occ S P E ps idx m n).2.getD l default =
      (PropElim.occ S P E ps idx m (l + 1)).2.getD l default := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hl : l = n
    · subst hl; rfl
    · rw [← ih (by omega)]
      have hlen := (PropElim.occ_length S P E ps idx m n).2
      simp only [PropElim.occ]
      split <;> rw [getD_append_left' (by omega)]

theorem _root_.Lean4Lean.PropElim.occ_getD_data (ps idx : List VExpr) (m : VExpr) {l k n : Nat}
    (hs : S.slot.getD l none = some k) (hl : l < n) :
    (PropElim.occ S P E ps idx m n).2.getD l default = idx.getD k default := by
  rw [PropElim.occ_getD_prefix ps idx m n hl]
  have hlen := (PropElim.occ_length S P E ps idx m l).2
  simp only [PropElim.occ, hs]
  rw [getD_append_right' (by omega), hlen, Nat.sub_self]
  rfl

end Literal

section Join
variable [Params]
open Params

set_option maxHeartbeats 1000000 in
/-- **Zero-source singleton coverage.** At a universe specialization where the
source of a large-eliminating recursor is `Prop`, its installed equation
is joined: the left side unfolds by the singleton prefix rule at the recursor
prefix and a beta step with the constructor major, and the result is normally
equal to the right side, the reconstructed data fields being the literal field
variables and the reconstructed proof fields being equal to them by proof
irrelevance. Needs canonical `Eq` for the typing of the extraction. -/
theorem RecursorRegistered.zero_join (heq : env.HasCanonicalEq) {Γ : List VExpr}
    {data : RecursorData} {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs)) (hlookup : recursorData data.name = some data)
    (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation)
    (hw : ∀ level ∈ levels, level.WF univs) (hl : levels.length = equation.uvars)
    (hlarge : data.largeTarget = true)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero) :
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right := by
  have hlen : levels.length = data.uvars := hl.trans (H.equation_uvars hgen)
  have hz : data.sourceLevel levels ≈ .zero := hzero
  have hdf := H.equation_present hgen
  obtain ⟨S, E, hS, hE, W⟩ := RecursorData.propElim_wf henv H hlarge hz hw hlen ⟨index, howner⟩
  obtain ⟨D, lb, rb, tb, X, hgen', hseq, hext, hD, hX, hlb, hio, hrt⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hz hlen howner hS hE
  rw [hgen'] at hgen
  cases Option.some.inj hgen
  have T := W.typed
  have hC := RecursorData.propElim_closed henv H hlarge hz hS hE
  obtain ⟨hidxl, hpl⟩ := RecursorData.singletonLayout_lengths hS
  have F := RecursorData.singletonSignature H hlarge hz
  -- names
  generalize hPdef : data.propParams levels = P at W hD hlb hio hC T hpl
  generalize hnf : S.fields.length = nf at hlb
  have hnf' : S.fields.length = nf := hnf
  generalize hnp : P.length = np at hlb hio
  have hnp' : P.length = np := hnp
  have hni : E.ctorIndices.length = S.indices.length := W.ctorIndices_length
  let D' := P ++ X ++ insertBinders S.fields 2
  have hD'len : D'.length = data.indexOffset + nf := by simp [D', hio, hX, hnf', hnp']; omega
  -- typing of the equation, in the empty context and in `Γ`
  have hexC := IsDefEq.extra (Γ := []) hdf hw hl
  have hexΓ := IsDefEq.extra (Γ := Γ) hdf hw hl
  simp only [VExpr.instL_wrapLams, VExpr.instL_wrapForalls, hD] at hexC hexΓ
  obtain ⟨hctxC, hlbC⟩ := HasType.wrapLams_inv henv (U := univs) (by trivial) hexC.hasType.1
  obtain ⟨hΔ, hlbΔ⟩ := HasType.wrapLams_inv henv hΓ hexΓ.hasType.1
  simp only [List.append_nil] at hctxC hlbC
  have hclD : ∀ j (h : j < D'.length), (D'[j]).ClosedN j := OnCtx.closed_reverse henv.ordered hctxC
  have hid : TelInst env univs (D'.reverse ++ Γ) D' (vars (data.indexOffset + nf) 0) := by
    have := TelInst.ident (env := env) (U := univs) Γ hclD
    rwa [hD'len, ← vars_eq_bvarRange'] at this
  -- the literal constructor instance beneath the equation's binders
  have hvars : vars (data.indexOffset + nf) 0 = vars np (2 + nf) ++ vars 2 nf ++ vars nf 0 := by
    rw [hio, vars_add, vars_add np 2]; simp
  have hf0 : TelInst env univs (D'.reverse ++ Γ) (P ++ S.fields) (vars np (2 + nf) ++ vars nf 0) := by
    refine TelInst.drop_mid (M := X) (m := vars 2 nf) ?_ (by simp [vars, hnp']) (by simp [vars, hX])
      T.scope.fields
    have h := hid
    rw [hvars] at h
    simpa only [D', insertBinders_eq_mapIdx, hX] using h
  have hpsl0 : (vars np (2 + nf)).length = P.length := by simp [vars, hnp']
  have hcI : ∀ x ∈ E.ctorIndices, x.ClosedN (np + nf) := fun x hx => by
    have := hC.ctorIndices x hx; rwa [hnp', hnf'] at this
  have hidx0 : E.ctorIndices.map (·.instOuter (vars np (2 + nf) ++ vars nf 0)) =
      E.ctorIndices.map (·.liftN 2 nf) := by
    apply List.map_congr_left; intro x hx
    simpa using instOuter_vars_skip (k := 0) (r := 2) (hcI x hx)
  have hargs0 := W.literal_args henv hpsl0 hf0
  rw [hidx0] at hargs0
  have hidxl0 : (E.ctorIndices.map (·.liftN 2 nf)).length = S.indices.length := by simp [hni]
  have hMc : HasType env univs (D'.reverse ++ Γ) (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0))
      (mkApps E.family (vars np (2 + nf) ++ E.ctorIndices.map (·.liftN 2 nf))) := by
    have h := TelInst.getD_mid (A := P ++ S.indices) (B := [PropElim.majorTy S P E]) (C := [])
      (a := vars np (2 + nf) ++ E.ctorIndices.map (·.liftN 2 nf))
      (b := [mkApps E.ctor (vars np (2 + nf) ++ vars nf 0)]) (c := [])
      (by simpa using hargs0) (by simp [hpsl0, hidxl0]) rfl (j := 0) (by simp)
    simpa [W.majorTy_instOuter hpsl0 hidxl0] using h
  rw [hio] at hlb
  rw [hlb] at hlbΔ hlbC
  -- the source prefix and its type
  obtain ⟨A, B, hsrcAB, hMcA⟩ := hlbΔ.app_inv henv.ordered hΔ
  obtain ⟨doms, body, hRT, hdl⟩ := RecursorData.recursorType_telescope hrt
  have hconst : env.HasType univs (D'.reverse ++ Γ) (.const data.name levels)
      (VExpr.wrapForalls (doms.map (·.instL levels)) (body.instL levels)) := by
    have := HasType.const (Γ := D'.reverse ++ Γ) F.recursor hw (by simpa using hlen)
    rwa [hRT, VExpr.instL_wrapForalls] at this
  have hprelen : (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)).length = data.majorOffset := by
    simp [vars, RecursorData.majorOffset, hio, hni, hidxl]
  have htf := VExpr.takeForalls_wrapForalls_append ((doms.map (·.instL levels)).take data.majorOffset)
    ((doms.map (·.instL levels)).drop data.majorOffset) (body.instL levels)
  rw [List.take_append_drop, List.length_take, List.length_map, hdl,
    Nat.min_eq_left (by omega), ← hprelen] at htf
  obtain ⟨res, hIF, hsrc⟩ := HasType.mkApps_telescope henv hΔ hconst ⟨_, hsrcAB⟩ htf
  have hsup := InstForallsC.supplyType_eq hIF
  obtain ⟨residual, doms2, tail, hsup2, hshape, hlen2⟩ :=
    RecursorData.supplyType_wrapForalls_exists
      (args := vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf))
      (domains := doms.map (·.instL levels)) (body := body.instL levels)
      (by simp only [List.length_map, hdl, hprelen]; omega)
  rw [hsup] at hsup2
  cases Option.some.inj hsup2
  rw [List.length_map, hdl, hprelen, Nat.add_sub_cancel_left] at hlen2
  obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hlen2
  subst hshape
  -- the opened major binder is the literal constructor instance's type
  have hsrcF : env.HasType univs (D'.reverse ++ Γ)
      ((VExpr.const data.name levels).mkApps (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)))
      (.forallE d tail) := hsrc
  have hdT := (IsType.forallE_inv henv.ordered (hsrcF.isType henv.ordered hΔ)).1
  have hΔ' : OnCtx (d :: (D'.reverse ++ Γ)) (env.IsType univs) := ⟨hΔ, hdT⟩
  have hdA : env.IsDefEqU univs (D'.reverse ++ Γ) d A := by
    obtain ⟨⟨u, h⟩, _⟩ := IsDefEqU.forallE_inv henv hΔ (hsrcF.uniqU henv hΔ hsrcAB)
    exact ⟨_, h⟩
  have hdF : env.IsDefEqU univs (D'.reverse ++ Γ) d
      (mkApps E.family (vars np (2 + nf) ++ E.ctorIndices.map (·.liftN 2 nf))) :=
    hdA.trans henv hΔ (hMcA.uniqU henv hΔ hMc)
  -- the opened instance
  have hidx1 : E.ctorIndices.map (·.instOuter (vars np (2 + nf + 1) ++ vars nf 1)) =
      (E.ctorIndices.map (·.liftN 2 nf)).map VExpr.lift := by
    rw [List.map_map]
    apply List.map_congr_left; intro x hx
    exact instOuter_vars_skip (k := 1) (r := 2) (hcI x hx)
  have hf1 : TelInst env univs (d :: (D'.reverse ++ Γ)) (P ++ S.fields)
      (vars np (2 + nf + 1) ++ vars nf 1) := by
    have h := TelInst.weak henv.ordered [d] (T.prefix_closed fun i h => T.scope.fields i h) hf0
    simpa [List.map_append, vars_map_lift] using h
  have hpsl1 : (vars np (2 + nf + 1)).length = P.length := by simp [vars, hnp']
  have hm1 : env.HasType univs (d :: (D'.reverse ++ Γ)) (.bvar 0)
      ((PropElim.majorTy S P E).instOuter (vars np (2 + nf + 1) ++
        E.ctorIndices.map (·.instOuter (vars np (2 + nf + 1) ++ vars nf 1)))) := by
    rw [W.majorTy_instOuter hpsl1 (by simp [hni])]
    have h0 : env.HasType univs (d :: (D'.reverse ++ Γ)) (.bvar 0) d.lift := .bvar .zero
    refine HasType.defeqU_r henv hΔ' ?_ h0
    have := hdF.weak henv.ordered (B := d)
    simpa [VExpr.liftN_mkApps, W.family_closed.liftN_eq (Nat.zero_le _), vars_map_lift, hidx1]
      using this
  have hslot := RecursorData.singleton_slot_lt H hlarge hz howner hS
  obtain ⟨hT1, hA1, hB1⟩ := W.literal_occ henv heq hslot hΔ' hpsl1 hf1 hm1
  generalize hidx1def : E.ctorIndices.map (·.instOuter (vars np (2 + nf + 1) ++ vars nf 1)) = idx1
    at hT1 hA1 hB1 hidx1
  generalize hocc1def : (PropElim.occ S P E (vars np (2 + nf + 1)) idx1 (.bvar 0)
    S.fields.length).2 = occ1 at hT1 hA1 hB1
  -- the generated program
  have hall : (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)).map (·.liftN 1) ++ vars 1 0 =
      vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0] := by
    have h1 : (vars (np + 2) nf).map (·.liftN 1) = vars np (2 + nf + 1) ++ vars 2 (nf + 1) := by
      rw [vars_add]
      simp only [List.map_append]
      rw [show (fun x : VExpr => x.liftN 1) = VExpr.lift from rfl, vars_map_lift, vars_map_lift]
    rw [List.map_append, h1, ← hidx1]
    simp [vars]
  have hidx1l : idx1.length = S.indices.length := by rw [← hidx1def]; simp [hni]
  have hrecon : data.singletonReconstruction env levels (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0]) =
      some (mkApps E.ctor (vars np (2 + nf + 1) ++ occ1), occ1) := by
    unfold RecursorData.singletonReconstruction
    have htake : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0]).take data.numParams =
        vars np (2 + nf + 1) := by
      rw [← hpl, hnp', List.append_assoc, List.append_assoc, List.take_left' (by simp [vars])]
    have hdrop : ((vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0]).drop data.indexOffset).take
        data.numIndices = idx1 := by
      rw [hio, show vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0] =
          (vars np (2 + nf + 1) ++ vars 2 (nf + 1)) ++ (idx1 ++ [VExpr.bvar 0]) by simp,
        List.drop_left' (by simp [vars]), ← hidxl, ← hidx1l, List.take_left]
    simp only [hS, hE, hPdef, bind, Option.bind_some, pure, htake, hdrop, hocc1def]
  have hocc1l : occ1.length = nf := by
    rw [← hocc1def, (PropElim.occ_length S P E _ _ _ _).2, hnf']
  have hDl : D.length = data.indexOffset + nf := by
    have := congrArg List.length hD
    simp only [List.length_map] at this
    rw [this]; exact hD'len
  have htakeio : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ idx1 ++ [VExpr.bvar 0]).take data.indexOffset =
      vars np (2 + nf + 1) ++ vars 2 (nf + 1) := by
    rw [hio, List.append_assoc, List.append_assoc, ← List.append_assoc (vars np _),
      List.take_left' (by simp [vars])]
  have hprog : data.singletonUnfolding env univs levels (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)) =
      some ⟨[d], tail, mkApps E.ctor (vars np (2 + nf + 1) ++ occ1),
        ⟨data.uvars, wrapLams D lb, wrapLams D rb, wrapForalls D tb⟩, ⟨D, lb, rb, tb⟩,
        vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1, levels⟩ := by
    unfold RecursorData.singletonUnfolding
    have hrem : data.majorOffset + 1 - (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)).length = 1 := by
      rw [hprelen]; omega
    have htk := RecursorData.takeForalls_wrapForalls [d] tail
    simp only [List.length_singleton] at htk
    have hsup' : RecursorData.supplyType (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf))
        ((data.recursorInstance.recursorType data.owner).instL levels) = some (wrapForalls [d] tail) := by
      rw [hRT, VExpr.instL_wrapForalls]; exact hsup
    rw [if_neg (by simp [hlen, hprelen])]
    simp only [hrt, bind, Option.bind_some]
    rw [hsup']
    simp only [Option.bind_some]
    rw [hrem, htk]
    simp only [Option.bind_some]
    rw [hall, hrecon]
    simp only [Option.bind_some]
    rw [htakeio, hseq, hgen']
    simp only [Option.bind_some]
    rw [hext]
    simp only [Option.bind_some]
    rw [if_neg (by simp [hocc1l, hDl, hio, vars]; omega)]
    rfl
  -- replay: the captures are a typed instance of the equation's binders
  have hcapT : TelInst env univs (d :: (D'.reverse ++ Γ)) D'
      (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1) := by
    have hidW := TelInst.weak henv.ordered [d] hclD hid
    have hv : (vars (data.indexOffset + nf) 0).map (·.liftN [d].length) =
        vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ vars nf 1 := by
      rw [hvars]
      simp only [List.length_singleton, List.map_append]
      rw [show (fun x : VExpr => x.liftN 1) = VExpr.lift from rfl, vars_map_lift, vars_map_lift,
        vars_map_lift]
    rw [hv] at hidW
    have HA : TelInst env univs (d :: (D'.reverse ++ Γ)) (P ++ X) (vars np (2 + nf + 1) ++ vars 2 (nf + 1)) := by
      have h := (show TelInst env univs (d :: (D'.reverse ++ Γ)) ((P ++ X) ++ insertBinders S.fields 2)
        ((vars np (2 + nf + 1) ++ vars 2 (nf + 1)) ++ vars nf 1) from hidW).take
      rwa [List.take_left' (by simp [vars, hnp', hX])] at h
    refine HA.append (by simp [hocc1l, hnf']) fun j hj => ?_
    simp only [InductiveSignature.Instance.length_insertBinders] at hj
    have h := TelInst.getD_mid (A := P) (a := vars np (2 + nf + 1)) (B := S.fields) (b := occ1)
      (C := []) (c := []) (by simpa using hT1) hpsl1 (by simp [hocc1l, hnf']) hj
    have hX' : (S.fields.getD j default).ClosedN (np + j) := by
      have := T.scope.fields_getD j; rwa [hnp'] at this
    have htl : (occ1.take j).length = j := by simp [hocc1l]; omega
    have hsk := instOuter_liftN_skip (X := S.fields.getD j default)
      (A := vars np (2 + nf + 1) ++ vars 2 (nf + 1)) (B := occ1.take j) (P := np) (r := 2)
      (by rw [htl]; exact hX') (by simp [vars])
    rw [htl, List.take_left' (by simp [vars])] at hsk
    rw [getD_of_lt (l := insertBinders S.fields 2) (by simpa using hj), getElem_insertBinders, ← getD_of_lt hj, hsk]
    exact h
  have hprop : env.HasType univs (d :: (D'.reverse ++ Γ))
      ((PropElim.majorTy S P E).instOuter (vars np (2 + nf + 1) ++ idx1)) (.sort .zero) := by
    have hI : TelInst env univs (d :: (D'.reverse ++ Γ)) (P ++ S.indices) (vars np (2 + nf + 1) ++ idx1) := by
      have h := (W.literal_args henv hpsl1 hf1).take
      rw [hidx1def, List.take_left' (by simp [hpsl1, hidx1l])] at h
      exact h
    have hctxI : OnCtx (P ++ S.indices).reverse (env.IsType univs) := by
      simpa using T.indicesCtx S.indices.length (Nat.le_refl _)
    simpa using HasType.closed_instOuter henv hctxI W.majorTy_typed hI
  -- replay: the opened source matches the equation's left side at the captures
  have hcapl : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1).length = D'.length := by
    rw [hD'len, hio]; simp [vars, hocc1l]; omega
  have hvl : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ vars nf 1).length = D'.length := by
    rw [hD'len, hio]; simp [vars]; omega
  have hpt : ∀ j, j < D'.length →
      env.IsDefEq univs (d :: (D'.reverse ++ Γ))
        ((vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1).getD j default)
        ((vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ vars nf 1).getD j default)
        ((D'.getD j default).instOuter ((vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1).take j)) := by
    intro j hj
    have hty := hcapT.getD hj
    by_cases hja : j < np + 2
    · rw [getD_append_left' (l₁ := vars np (2 + nf + 1) ++ vars 2 (nf + 1)) (by simp [vars]; omega),
        getD_append_left' (l₁ := vars np (2 + nf + 1) ++ vars 2 (nf + 1)) (by simp [vars]; omega)]
      rw [getD_append_left' (l₁ := vars np (2 + nf + 1) ++ vars 2 (nf + 1)) (by simp [vars]; omega)] at hty
      exact hty
    · have hl2 : (vars np (2 + nf + 1) ++ vars 2 (nf + 1)).length = np + 2 := by simp [vars]
      obtain ⟨l, rfl⟩ : ∃ l, j = np + 2 + l := ⟨j - (np + 2), by omega⟩
      have hlnf : l < nf := by rw [hD'len, hio] at hj; omega
      rw [getD_append_right' (by omega), getD_append_right' (by omega), hl2, Nat.add_sub_cancel_left]
      have h := hA1 l (by omega)
      have hD'j : D'.getD (np + 2 + l) default = (insertBinders S.fields 2).getD l default := by
        simp only [D']
        rw [getD_append_right' (by simp [hnp', hX]), show np + 2 + l - (P ++ X).length = l by
          simp [hnp', hX]]
      have hX' : (S.fields.getD l default).ClosedN (np + l) := by
        have := T.scope.fields_getD l; rwa [hnp'] at this
      have htl : (occ1.take l).length = l := by simp [hocc1l]; omega
      have hsk := instOuter_liftN_skip (X := S.fields.getD l default)
        (A := vars np (2 + nf + 1) ++ vars 2 (nf + 1)) (B := occ1.take l) (P := np) (r := 2)
        (by rw [htl]; exact hX') (by simp [vars])
      rw [htl, List.take_left' (by simp [vars])] at hsk
      rw [hD'j, getD_of_lt (l := insertBinders S.fields 2) (by simp [hnf']; omega),
        getElem_insertBinders, ← getD_of_lt (by omega), List.take_append, List.take_of_length_le (by omega), hl2,
        Nat.add_sub_cancel_left, hsk]
      exact h
  have hctxCl := CtxWF.closed henv.ordered hctxC
  have hpreT : ∀ x ∈ vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf),
      env.IsDefEqU univs (d :: (D'.reverse ++ Γ)) x.lift
        (x.instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)) := by
    intro x hx
    obtain ⟨_, _, hsC, _⟩ := hlbC.app_inv henv.ordered hctxC
    obtain ⟨Tx, hxT⟩ := HasType.mkApps_args_typed hctxC hsC x hx
    have hxc : x.ClosedN (np + 2 + nf) := by
      have h0 := (hxT.closedN' henv.ordered.closed hctxCl).1
      exact h0.mono (by simp [hnf', hX, hnp']; omega)
    have h := IsDefEq.closed_instOuter_congr' henv hΔ' hctxC hxT hcapl hvl hpt
    have hlift : x.instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ vars nf 1) = x.lift := by
      rw [show x.lift = x.liftN 1 from rfl, ← instOuter_vars_lift (k := 1) hxc, vars_add, vars_add np 2,
        show 2 + (nf + 1) = 2 + nf + 1 by omega]
    rw [hlift] at h
    exact ⟨_, h.symm⟩
  have hMcI : (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0)).instOuter
      (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1) = mkApps E.ctor (vars np (2 + nf + 1) ++ occ1) := by
    have hl : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1).length = np + 2 + nf := by
      simp [vars, hocc1l]; omega
    have e1 : (vars np (2 + nf)).map (·.instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)) =
        vars np (2 + nf + 1) := by
      rw [map_instOuter_vars _ _ _ (by omega), hl, show np + 2 + nf - (np + (2 + nf)) = 0 by omega,
        List.drop_zero, List.append_assoc, List.take_left' (by simp [vars])]
    have e2 : (vars nf 0).map (·.instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)) = occ1 := by
      rw [map_instOuter_vars _ _ _ (by omega), hl,
        show np + 2 + nf - (nf + 0) = (vars np (2 + nf + 1) ++ vars 2 (nf + 1)).length by simp [vars],
        List.drop_left, List.take_of_length_le (by simp [hocc1l])]
    rw [VExpr.instOuter_mkApps, instOuter_closed0 W.ctor_closed, List.map_append, e1, e2]
  have hlhs : ConstSpineDefEq env univs (d :: (D'.reverse ++ Γ))
      (.app ((VExpr.const data.name levels).mkApps (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf))).lift
        (mkApps E.ctor (vars np (2 + nf + 1) ++ occ1)))
      ((lb.instL levels).instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)) := by
    rw [hlb]
    refine ⟨data.name, levels, levels,
      (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)).map VExpr.lift ++
        [mkApps E.ctor (vars np (2 + nf + 1) ++ occ1)],
      (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf)).map
        (·.instOuter (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)) ++
        [mkApps E.ctor (vars np (2 + nf + 1) ++ occ1)], ?_, ?_, hw, hw,
      Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl), ?_⟩
    · rw [VExpr.mkApps_snoc]; simp [VExpr.liftN_mkApps, VExpr.liftN]
    · rw [← VExpr.mkApps_snoc, VExpr.instOuter_mkApps, VExpr.instOuter_const, List.map_append,
        List.map_singleton, hMcI]
    · refine List.Forall₂.append' ?_ (.cons ⟨_, hB1.hasType.2⟩ .nil)
      exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (Lean4Lean.List.Forall₂.rfl hpreT))
  have hDj : ∀ j (h : j < D.length), D[j].instL levels = D'[j]'(by rw [hD'len, ← hDl]; exact h) := by
    intro j h
    simp only [D', ← hD, List.getElem_map]
  have hrule : PrefixUnfold env univs recursorData (D'.reverse ++ Γ) data.name levels
      (vars (np + 2) nf ++ E.ctorIndices.map (·.liftN 2 nf))
      (VExpr.wrapLams [d] (instantiateParams (rb.instL levels)
        (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1))) := by
    refine PrefixUnfold.intro hlookup H rfl hlarge hw hz hprog ?_
    refine ⟨hsrc, by simp, hdf, hext, hw, hl, by simp [hocc1l, hDl, hio, vars]; omega, ?_,
      ⟨_, hprop, hB1.hasType.1, hB1.hasType.2⟩, hlhs⟩
    intro j hj hd
    have h := hcapT.2 j hj (by rw [← hcapl]; exact hj)
    simp only at hd ⊢
    rw [hDj j hd]
    exact h
    -- the beta contractum: the right side at the reconstructed fields of the literal instance
  have hm0 : env.HasType univs (D'.reverse ++ Γ) (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0))
      ((PropElim.majorTy S P E).instOuter (vars np (2 + nf) ++
        E.ctorIndices.map (·.instOuter (vars np (2 + nf) ++ vars nf 0)))) := by
    rw [hidx0, W.majorTy_instOuter hpsl0 hidxl0]; exact hMc
  obtain ⟨hT0, hA0, -⟩ := W.literal_occ henv heq hslot hΔ hpsl0 hf0 hm0
  have hlit0 := fun {l k : Nat} (hs : S.slot.getD l none = some k) (hlf : l < S.fields.length) =>
    W.literal_index (ps := vars np (2 + nf)) (f := vars nf 0) (by simp [vars, hnp', hnf']) hpsl0 hs hlf
  rw [hidx0] at hT0 hA0 hlit0
  generalize hocc0def : (PropElim.occ S P E (vars np (2 + nf)) (E.ctorIndices.map (·.liftN 2 nf))
    (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0)) S.fields.length).2 = occ0 at hT0 hA0
  have hocc0l : occ0.length = nf := by
    rw [← hocc0def, (PropElim.occ_length S P E _ _ _ _).2, hnf']
  -- closedness of the right side
  obtain ⟨-, hrbC⟩ := HasType.wrapLams_inv henv (U := univs) (by trivial) hexC.hasType.2
  simp only [List.append_nil] at hrbC
  have hrbc : (rb.instL levels).ClosedN (np + 2 + nf) := by
    have h0 := (hrbC.closedN' henv.ordered.closed hctxCl).1
    exact h0.mono (by simp [hnf', hX, hnp']; omega)
  have hbeta : (instantiateParams (rb.instL levels) (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1)).inst
      (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0)) =
      instantiateParams (rb.instL levels) (vars np (2 + nf) ++ vars 2 nf ++ occ0) := by
    have hτ : ∀ x : VExpr, x.inst (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0)) =
        x.subst (.liftN (.one (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0))) 0) :=
      fun x => VExpr.instN_eq _ _
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter, hτ,
      instOuter_subst_closed _ _ (by
        have : (vars np (2 + nf + 1) ++ vars 2 (nf + 1) ++ occ1).length = np + 2 + nf := by
          simp [vars, hocc1l]; omega
        rw [this]; exact hrbc)]
    congr 1
    have hsc : S.Scoped (vars np (2 + nf + 1)).length := by rw [hpsl1]; exact hC.scope
    have hsub := (PropElim.occ_subst (m := VExpr.bvar 0) hC hsc hidx1l
      (.liftN (.one (mkApps E.ctor (vars np (2 + nf) ++ vars nf 0))) 0) S.fields.length (Nat.le_refl _)).2
    simp only [← hτ] at hsub
    rw [hocc1def] at hsub
    simp only [List.map_append, ← hτ, hsub, vars_map_inst_succ]
    rw [hidx1, List.map_map]
    simp only [Function.comp_def, VExpr.inst_lift, List.map_id_fun', id]
    rw [← hocc0def]
    simp [VExpr.inst, VExpr.instVar]
  have hred : FullReduction (D'.reverse ++ Γ) (lb.instL levels)
      (instantiateParams (rb.instL levels) (vars np (2 + nf) ++ vars 2 nf ++ occ0)) := by
    rw [← hbeta, hlb]
    exact .tail (.tail .rfl (.app (.delta hrule) .rfl)) (.core (.beta .rfl .rfl))
  -- normal equality with the right side
  have hvarsT : ∀ a ∈ vars np (2 + nf) ++ vars 2 nf, ∃ A, env.HasType univs (D'.reverse ++ Γ) a A := by
    intro a ha
    have ha' : a ∈ vars (data.indexOffset + nf) 0 := by rw [hvars]; exact List.mem_append_left _ ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha'
    exact ⟨_, hid.2 j hj (by rw [← hid.1]; exact hj)⟩
  have hfields : List.Forall₂ (NormalEqF true (D'.reverse ++ Γ)) occ0 (vars nf 0) := by
    refine forall₂_of_getElem (by simp [hocc0l, vars]) fun l h1 h2 => ?_
    have hl : l < S.fields.length := by rw [hnf']; rw [hocc0l] at h1; exact h1
    have hty := TelInst.getD_mid (A := P) (B := S.fields) (C := []) (a := vars np (2 + nf)) (b := occ0)
      (c := []) (by rw [List.append_nil, List.append_nil]; exact hT0) hpsl0 (by simp [hocc0l, hnf']) hl
    rw [← getD_of_lt h1, ← getD_of_lt h2]
    cases hs : S.slot.getD l none with
    | some k =>
      have he : occ0.getD l default = (vars nf 0).getD l default := by
        rw [← hocc0def, PropElim.occ_getD_data _ _ _ hs hl, hlit0 hs hl]
      rw [he]; rw [he] at hty; exact .refl hty
    | none =>
      have hp : env.HasType univs (D'.reverse ++ Γ)
          ((S.fields.getD l default).instOuter (vars np (2 + nf) ++ occ0.take l)) (.sort .zero) := by
        have hfs := T.fieldSort l hl
        simp only [SingletonLayout.fieldSort, hs] at hfs
        have hctxL := T.fieldsCtx l (Nat.le_of_lt hl)
        have hTl : TelInst env univs (D'.reverse ++ Γ) (P ++ S.fields.take l)
            (vars np (2 + nf) ++ occ0.take l) := by
          have h0 : TelInst env univs (D'.reverse ++ Γ) ((P ++ S.fields.take l) ++ S.fields.drop l)
              (vars np (2 + nf) ++ occ0) := by
            rw [List.append_assoc, List.take_append_drop]; exact hT0
          have h := h0.take
          have hlen : (P ++ S.fields.take l).length = (vars np (2 + nf)).length + l := by
            simp [hpsl0]; omega
          rwa [hlen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left] at h
        have := HasType.closed_instOuter henv hctxL hfs hTl
        rw [← getD_of_lt hl] at this; simpa using this
      exact .proofIrrel hp hty (hA0 l hl).hasType.2
  have hnorm : NormalEq (D'.reverse ++ Γ)
      (instantiateParams (rb.instL levels) (vars np (2 + nf) ++ vars 2 nf ++ occ0)) (rb.instL levels) := by
    have hht := hred.hasType hΔ (by rw [hlb]; exact hlbΔ)
    have h := NormalEqF.instantiateParams_args hΔ
      (List.Forall₂.append' (NormalEqF.forall₂_refl hvarsT) hfields) hht
    have hid' : instantiateParams (rb.instL levels) (vars np (2 + nf) ++ vars 2 nf ++ vars nf 0) =
        rb.instL levels := by
      rw [← hvars, instantiateParams_eq_instOuter, hio, instOuter_vars_lift hrbc, VExpr.liftN_zero]
    rwa [hid'] at h
  refine ⟨VExpr.wrapLams D' (instantiateParams (rb.instL levels) (vars np (2 + nf) ++ vars 2 nf ++ occ0)),
    _, ?_, .rfl, ?_⟩
  · show FullReduction Γ ((VExpr.wrapLams D lb).instL levels) _
    simp only [VExpr.instL_wrapLams, hD]
    exact FullReduction.wrapLams' hred
  · show NormalEq Γ _ ((VExpr.wrapLams D rb).instL levels)
    simp only [VExpr.instL_wrapLams, hD]
    obtain ⟨u, hu⟩ := hexΓ.hasType.1.isType henv.ordered hΓ
    exact NormalEqF.wrapLams_congr hΓ rfl ⟨_, hu⟩ hnorm

end Join

end Lean4Lean.VEnv
