import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.Typing.PrefixUnfolding.ArgumentCongruence
import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationSupply
import Lean4Lean.Theory.Typing.Confluence.RegistryMetadata
import Lean4Lean.Theory.LevelledConfluence
import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Inductive.CaseCapture
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.LevelledReduction
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Inductive.Signature

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]
section Basic
omit [Params] in
theorem forall₂_of_getElem {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i]) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hlen, H =>
    .cons (H 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using hlen) fun i hi hi' => H (i + 1) (by simpa using hi)
        (by simpa using hi'))
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
end Basic
end Lean4Lean.VEnv

/-! Coverage of the installed generated iota equations by the full presentation.

A restored recursor equation is a lambda telescope over the recursor's
parameters, motives and minors and the constructor's fields; its left side
applies the recursor to the first of these binders, the constructor's indices
and the constructor applied to (possibly specialized) parameters followed by
its field binders. At every universe specialization whose source level is not
zero, or for a small target, the generated iota pattern reduces the body to the
right side applied to all binders, which beta-reduces to the right side. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature
open private restored_constructor_arguments restoration_vars
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas

/-- The restoration of a registered recursor instance specializes exactly the
signature's common parameters. -/
theorem RecursorRegistered.restoration_nparams {data : RecursorData}
    (H : RecursorRegistered env data) :
    ∀ head ∈ data.schema.restoration.heads, head.nparams = data.schema.signature.params.length := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _⟩ := H
  intro head hhead
  rw [hr] at hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  have hn := hdata.model.nparams.trans hdata.nparams
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm

private theorem vars_join' (p f : Nat) : vars p f ++ vars f 0 = vars (p + f) 0 := by
  rw [Nat.add_comm p f]
  simp [vars, List.range_add, List.reverse_append, List.map_append, List.map_map]

/-- The exact syntax of a restored recursor equation. -/
theorem RecursorRegistered.equation_shape {data : RecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) :
    ∃ domains idx cl cp rhsBody typeBody,
      equation.lhs = VExpr.wrapLams domains (.app
        (VExpr.mkApps (.const data.name (VLevel.params data.uvars))
          (vars data.indexOffset data.schema.signature.constructors[index].fields.length ++ idx))
        (VExpr.mkApps (.const (data.ruleConstructor index) cl)
          (cp ++ vars data.schema.signature.constructors[index].fields.length 0))) ∧
      equation.rhs = VExpr.wrapLams domains rhsBody ∧
      equation.type = VExpr.wrapForalls domains typeBody ∧
      domains.length = data.indexOffset + data.schema.signature.constructors[index].fields.length ∧
      idx.length = data.schema.signature.constructors[index].indices.length := by
  let r := data.schema.restoration
  let g := data.recursorInstance
  let s := data.schema.signature
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let major := g.constructorApp ctor extra 0
  have hrestore : r.equation (g.equation index) = some equation := hgen
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  have hdomlen : domains.length = np + nf := by
    simp only [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, InductiveSignature.fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList]
    simp only [np, nf, extra, s, ctor]
    omega
  have hnp : np = data.indexOffset := by
    simp only [np, extra, s, RecursorData.indexOffset, RecursorData.numParams,
      Nat.add_assoc]
  obtain ⟨ds', lhs', rhs', type', hl', hr', ht', hel, her, het, hlen⟩ :=
    restored_common_telescope hl hr ht
  have hlhs0 : r.expr (VExpr.mkApps (g.recursorHead .recursor ctor.owner)
      (vars np nf ++ indices ++ [major])) = some lhs' := hl'
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp [List.mapM_append, restoration_vars, List.mapM_cons, Restoration.expr.go] at hlhs0
  obtain ⟨allArgs, ⟨restArgs, ⟨indices', hi, majorArgs, ⟨major', hmajor, rfl⟩, rfl⟩, rfl⟩, hout⟩ := hlhs0
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    obtain ⟨base, installBase, source, expanded, g', auxiliaries, block, installed,
      hdata, _, _, hr0, _, hu, hl0, ht0, _⟩ := H
    have hinst : data.recursorInstance = g' := by
      cases g' with
      | mk U levels target recNames =>
        simp only [RecursorData.recursorInstance, Instance.mk.injEq]
        exact ⟨hu, hl0, ht0, funext fun owner => (hdata.recursorNames owner).symm⟩
    apply List.find?_eq_none.mpr
    intro spec hs
    have := hdata.heads_not_recursors ctor.owner spec (by rw [← hr0]; exact hs)
    simpa only [beq_iff_eq, g, hinst] using this
  have hlhs : lhs' = .app
      (VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars))
        (vars np nf ++ indices')) major' := by
    simpa [Instance.recursorHead, Restoration.expr.go, hnone, VExpr.mkApps,
      List.foldl_append] using hout.symm
  have hparams : ∀ h ∈ r.heads, h.nparams ≤ s.params.length := fun h hh =>
    Nat.le_of_eq (H.restoration_nparams h hh)
  obtain ⟨cn, cl, cp, hc⟩ := restored_constructor_arguments hparams hmajor
  obtain ⟨cl', ca', hca⟩ := r.const_mkApps hmajor
  have hmajor' : major' = VExpr.mkApps (.const (r.headName ctor.name) cl) (cp ++ vars nf 0) := by
    rw [hca] at hc ⊢
    rw [spine_mkApps_exact _ _ rfl] at hc
    cases hc
    rfl
  have hidx : indices'.length = ctor.indices.length := by
    have length_eq : ∀ {xs ys}, List.Forall₂ (fun x y => r.expr x = some y) xs ys →
        ys.length = xs.length := by
      intro xs ys hrel
      induction hrel with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    simpa [indices] using length_eq (List.mapM_eq_some.mp hi)
  refine ⟨ds', indices', cl, cp, rhs', type', ?_, her, het, ?_, hidx⟩
  · rw [hel, hlhs, hmajor']
    have hname : r.recursorName (g.recursorName ctor.owner) = data.name := by
      show r.recursorName (data.schema.signature.families[
        data.schema.signature.constructors[index].owner].name.str "rec") = _
      simp only [howner]; rfl
    rw [hname, hnp]
    rfl
  · rw [hlen, hdomlen, hnp]

theorem RecursorRegistered.constructor_indices_length {data : RecursorData}
    (H : RecursorRegistered env data) (index : Fin data.schema.signature.constructors.size) :
    data.schema.signature.constructors[index].indices.length =
      data.schema.signature.families[data.schema.signature.constructors[index].owner].indices.length := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _⟩ := H
  exact hdata.model.constructorArity _ (by simp)

theorem vars_eq_bvarRange' (n : Nat) : vars n 0 = VExpr.bvarRange n n := by
  apply List.ext_getElem
  · simp [vars, VExpr.bvarRange]
  · intro i hi hi'
    simp [vars, VExpr.bvarRange] at hi hi' ⊢

theorem vars_instL (n k : Nat) (ls : List VLevel) : (vars n k).map (VExpr.instL ls) = vars n k := by
  simp [vars, List.map_map, Function.comp_def, VExpr.instL]

theorem closedN_wrapLams_body {domains : List VExpr} {body : VExpr}
    (h : (VExpr.wrapLams domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapLams domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

section
variable [Params]
open Params

theorem ParRedS.wrapLams' (H : ParRedS (domains.reverse ++ Γ) body body') :
    ParRedS Γ (VExpr.wrapLams domains body) (VExpr.wrapLams domains body') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (ParRed.wrapLams h)

theorem ParRed.mkApps_left' (H : ParRed Γ f f') : ParRed Γ (VExpr.mkApps f as) (VExpr.mkApps f' as) := by
  induction as generalizing f f' with
  | nil => exact H
  | cons a as ih => exact ih (.app H .rfl)

theorem ParRedS.mkApps_wrapLams : ∀ {args doms : List VExpr} {body : VExpr},
    args.length = doms.length →
    ParRedS Γ (VExpr.mkApps (VExpr.wrapLams doms body) args) (body.instOuter args)
  | [], [], _, _ => .rfl
  | a :: as, d :: ds, body, hlen => by
    have hlen' : as.length = ds.length := by simpa using hlen
    have hstep : ParRed Γ (VExpr.mkApps (VExpr.wrapLams (d :: ds) body) (a :: as))
        (VExpr.mkApps ((VExpr.wrapLams ds body).inst a) as) :=
      ParRed.mkApps_left' (.beta .rfl .rfl)
    have ih := ParRedS.mkApps_wrapLams (Γ := Γ) (args := as) (doms := VExpr.instDomains ds a 0)
      (body := body.inst a ds.length) (by simpa [VExpr.instDomains] using hlen')
    rw [VExpr.wrapLams_inst] at hstep
    simp only [Nat.zero_add] at hstep
    rw [VExpr.instOuter_cons, hlen']
    exact (ReflTransGen.tail .rfl hstep).trans ih
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

end

theorem _root_.Lean4Lean.Pattern.argumentRHS_apply_levels (p : Pattern) (n : Nat)
    (l l' : List VLevel) (g : (p.varN n).Path → VExpr) :
    (p.argumentRHS n).map (·.apply l g) = (p.argumentRHS n).map (·.apply l' g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : ∀ (lv : List VLevel), (p.argumentRHS n).map
        (fun x => Pattern.RHS.apply lv g (Pattern.RHS.mapPaths some x)) =
        (p.argumentRHS n).map (fun x => x.apply lv (g ∘ some)) :=
      fun lv => List.map_congr_left (fun x _ => Pattern.RHS.mapPaths_apply _ _)
    simp only [Pattern.argumentRHS, List.map_append, List.map_map, Function.comp_def,
      List.map_cons, List.map_nil, Pattern.RHS.apply]
    rw [hm l, hm l', ih]

theorem stripLams_wrapLams_app (domains : List VExpr) (f a : VExpr) :
    (VExpr.wrapLams domains (.app f a)).stripLams = .app f a := by
  induction domains with
  | nil => rfl
  | cons _ _ ih => exact ih

section
variable [Params]
open Params

/-- An installed recursor equation reduces by its own generated iota pattern at
every universe specialization that passes the large-elimination guard. -/
theorem RecursorRegistered.equation_parRedS {data : RecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    {levels : List VLevel}
    (hpat : ∀ {p r}, GeneratedIotaPattern env recursorData p r → Pat p r)
    (hlookup : recursorData data.name = some data) (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation)
    (hlen : levels.length = data.uvars)
    (hguard : data.largeTarget = true →
      ¬((data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero)) :
    ParRedS Γ (equation.lhs.instL levels) (equation.rhs.instL levels) := by
  obtain ⟨domains, idx, cl, cp, rb, tb, hl, hr, -, hdl, hidx⟩ := H.equation_shape howner hgen
  have hclosed := H.equation_closed henv hgen
  have hcl := hclosed.2.1
  rw [hr] at hcl
  have hrb := closedN_wrapLams_body hcl
  simp only [Nat.zero_add] at hrb
  let nf := data.schema.signature.constructors[index].fields.length
  let io := data.indexOffset
  let cc := data.ruleConstructor index
  let pre := vars io nf ++ idx.map (VExpr.instL levels)
  let cargs := cp.map (VExpr.instL levels) ++ vars nf 0
  have hhead : (VLevel.params data.uvars).map (VLevel.inst levels) = levels :=
    VLevel.inst_map_id hlen
  have hbody : (VExpr.app
      (VExpr.mkApps (.const data.name (VLevel.params data.uvars)) (vars io nf ++ idx))
      (VExpr.mkApps (.const cc cl) (cp ++ vars nf 0))).instL levels =
      .app (VExpr.mkApps (.const data.name levels) pre)
        (VExpr.mkApps (.const cc (cl.map (·.inst levels))) cargs) := by
    simp only [VExpr.instL, VExpr.instL_mkApps, List.map_append, vars_instL, hhead, pre, cargs]
  have hpre : pre.length = data.majorOffset := by
    have hi := H.constructor_indices_length index
    simp only [howner] at hi
    simp only [pre, List.length_append, List.length_map, hidx, hi, vars, List.length_reverse,
      List.length_range, io, RecursorData.majorOffset, RecursorData.numIndices]
  have hmajorArgs : RecursorData.ruleMajorArguments equation = cp ++ vars nf 0 := by
    unfold RecursorData.ruleMajorArguments
    rw [hl]
    rw [stripLams_wrapLams_app, ← VExpr.mkApps_snoc,
      InductiveSignature.spine_mkApps_exact (.const data.name (VLevel.params data.uvars)) _ rfl]
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
    rw [InductiveSignature.spine_mkApps_exact (.const cc cl) _ rfl]
  have hcargs : cargs.length = (RecursorData.ruleMajorArguments equation).length := by
    simp [cargs, hmajorArgs]
  obtain ⟨g1, hg1⟩ := Pattern.Matches.constVarN_exists (c := data.name) data.majorOffset
    (vs := pre) (ls := levels) hpre
  obtain ⟨g2, hg2⟩ := Pattern.Matches.constVarN_exists (c := cc)
    (RecursorData.ruleMajorArguments equation).length (vs := cargs)
    (ls := cl.map (·.inst levels)) hcargs
  have hm : (data.rulePattern index equation).Matches
      (.app (VExpr.mkApps (.const data.name levels) pre)
        (VExpr.mkApps (.const cc (cl.map (·.inst levels))) cargs)) levels (Sum.elim g1 g2) :=
    .app hg1 hg2
  have hp := hpat (GeneratedIotaPattern.intro henv H hlookup howner hgen)
  have hck : ∀ df, Pattern.Check.OK (p := data.rulePattern index equation) df levels (Sum.elim g1 g2)
      (data.ruleCheck index equation) := by
    intro df
    unfold RecursorData.ruleCheck
    split
    · exact ⟨hguard (by assumption), trivial⟩
    · trivial
  let Δ := (domains.map (VExpr.instL levels)).reverse ++ Γ
  have step := ParRed.extra (Γ := Δ) hp hm (hck _) (fun _ => .rfl)
  have hpreEq := (mkApps_const_inj hg1.const_arguments).2.2
  have hcEq := (mkApps_const_inj hg2.const_arguments).2.2
  have hcapt : (RecursorData.ruleCaptures data index equation).map
      (fun (x : (data.rulePattern index equation).RHS) =>
          Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2) x) =
      vars (io + nf) 0 := by
    unfold RecursorData.ruleCaptures
    rw [List.map_append, List.map_map, List.map_map]
    have e1 : ∀ l : List ((Pattern.const data.name).varN data.majorOffset).RHS,
        l.map ((fun (x : (data.rulePattern index equation).RHS) =>
          Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2) x) ∘
          Pattern.RHS.mapPaths Sum.inl) = l.map (fun x => x.apply levels g1) :=
      fun l => List.map_congr_left (fun x _ => Pattern.RHS.mapPaths_apply _ _)
    have e2 : ∀ l : List ((Pattern.const cc).varN
          (RecursorData.ruleMajorArguments equation).length).RHS,
        l.map ((fun (x : (data.rulePattern index equation).RHS) =>
          Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2) x) ∘
          Pattern.RHS.mapPaths Sum.inr) = l.map (fun x => x.apply levels g2) :=
      fun l => List.map_congr_left (fun x _ => Pattern.RHS.mapPaths_apply _ _)
    rw [e1, e2]
    have h1 : (((Pattern.const data.name).argumentRHS data.majorOffset).take data.indexOffset).map
        (fun x => x.apply levels g1) = vars io nf := by
      rw [List.map_take, ← hpreEq]
      simp only [pre, io]
      exact List.take_left' (by simp [vars])
    have h2 : (((Pattern.const cc).argumentRHS (RecursorData.ruleMajorArguments equation).length).drop
        ((RecursorData.ruleMajorArguments equation).length -
          data.schema.signature.constructors[index].fields.length)).map
        (fun x => x.apply levels g2) = vars nf 0 := by
      rw [List.map_drop, Pattern.argumentRHS_apply_levels (l' := cl.map (·.inst levels)),
        ← hcEq]
      simp only [cargs, hmajorArgs, List.length_append]
      rw [show cp.length + (vars nf 0).length - nf = (cp.map (VExpr.instL levels)).length by
        simp [vars]]
      exact List.drop_left
    rw [h1, h2, vars_join']
  have happly : Pattern.RHS.apply (p := data.rulePattern index equation) levels (Sum.elim g1 g2)
      (data.ruleRHS index equation hclosed.2.1) =
      VExpr.mkApps (equation.rhs.instL levels) (vars (io + nf) 0) := by
    unfold RecursorData.ruleRHS
    refine (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).trans ?_
    rw [hcapt]
    rfl
  rw [hl, hr, VExpr.instL_wrapLams, VExpr.instL_wrapLams]
  apply ParRedS.wrapLams'
  change ParRedS Δ _ _
  rw [hbody]
  refine (ReflTransGen.tail .rfl step).trans ?_
  change ParRedS Δ (Pattern.RHS.apply (p := data.rulePattern index equation) levels
    (Sum.elim g1 g2) (data.ruleRHS index equation hclosed.2.1)) _
  rw [happly, hr, VExpr.instL_wrapLams]
  have hn : (vars (io + nf) 0).length = (domains.map (VExpr.instL levels)).length := by
    simp [vars, hdl, io, nf]
  refine (ParRedS.mkApps_wrapLams hn).trans ?_
  have hrb' : (rb.instL levels).ClosedN (io + nf) := by
    have := hrb.instL (ls := levels); rwa [hdl] at this
  rw [vars_eq_bvarRange', VExpr.instOuter_range_bvar' _ _ _ hrb' (Nat.le_refl _), Nat.sub_self,
    VExpr.liftN_zero]
  exact .rfl

/-- Coverage of a recursor equation at a guarded universe specialization. -/
theorem RecursorRegistered.equation_join {data : RecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    {levels : List VLevel}
    (hpat : ∀ {p r}, GeneratedIotaPattern env recursorData p r → Pat p r)
    (hlookup : recursorData data.name = some data) (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation)
    (hw : ∀ level ∈ levels, level.WF univs) (hlen : levels.length = equation.uvars)
    (hguard : data.largeTarget = true →
      ¬((data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero)) :
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right := by
  have hlen' : levels.length = data.uvars := hlen.trans (H.equation_uvars hgen)
  have hred := (H.equation_parRedS (Γ := Γ) hpat hlookup howner hgen hlen' hguard).full
  have hex := IsDefEq.extra (Γ := Γ) (H.equation_present hgen) hw hlen
  exact ⟨_, _, hred, .rfl, .refl hex.hasType.2⟩

end

end Lean4Lean.VEnv
