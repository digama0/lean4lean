import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas

namespace Lean4Lean
namespace VExpr

private theorem reduction_head_go (e : VExpr) (args : List VExpr) :
    (getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app f a ih _ => exact (ih (a :: args)).trans (ih [a]).symm
  | _ => rfl

private theorem reduction_head_app (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs.1 = fn.getAppFnArgs.1 := reduction_head_go fn [arg]

private theorem reduction_head_mkApps (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => simpa only [mkApps, List.foldl_cons, reduction_head_app] using ih (.app fn a)

end VExpr
namespace InductiveSignature

private theorem restored_const_head {r : Restoration} {e output : VExpr}
    {args : List VExpr} (hhead : e.getAppFnArgs.1 = .const name levels)
    (h : Restoration.expr.go r e args = some output) :
    ∃ name levels, output.getAppFnArgs.1 = .const name levels := by
  induction e generalizing args with
  | app fn arg ih _ =>
    rw [VExpr.reduction_head_app] at hhead
    change (do let arg' ← r.expr arg; Restoration.expr.go r fn (arg' :: args)) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', _, h⟩ := h
    exact ih hhead h
  | const n ls =>
    simp only [Restoration.expr.go] at h
    split at h
    · rename_i spec hs
      simp only [HeadSpecialization.apply] at h
      split at h
      · cases h
      · cases h
        exact ⟨_, _, VExpr.reduction_head_mkApps _ _⟩
    · cases h
      exact ⟨_, _, VExpr.reduction_head_mkApps _ _⟩
  | _ => cases hhead

private theorem restored_elim_spine {r : Restoration} {e output : VExpr}
    {args : List VExpr} (hhead : e.getAppFnArgs.1 = .elim block owner levels)
    (h : Restoration.expr.go r e args = some output) :
    ∃ preArgs, output = VExpr.mkApps (.elim block owner levels) (preArgs ++ args) := by
  induction e generalizing args with
  | app fn arg ih _ =>
    rw [VExpr.reduction_head_app] at hhead
    change (do let arg' ← r.expr arg; Restoration.expr.go r fn (arg' :: args)) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', _, h⟩ := h
    obtain ⟨preArgs, rfl⟩ := ih hhead h
    exact ⟨preArgs ++ [arg'], by simp⟩
  | elim b o ls =>
    have heq : b = block ∧ o = owner ∧ ls = levels := by
      simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using hhead
    obtain ⟨rfl, rfl, rfl⟩ := heq
    cases h
    exact ⟨[], rfl⟩
  | _ => cases hhead

theorem restored_common_telescope {r : Restoration} {domains : List VExpr}
    {lhs rhs type lhs' rhs' type' : VExpr}
    (hl : r.expr (VExpr.wrapLams domains lhs) = some lhs')
    (hr : r.expr (VExpr.wrapLams domains rhs) = some rhs')
    (ht : r.expr (VExpr.wrapForalls domains type) = some type') :
    ∃ domains' l r' t, r.expr lhs = some l ∧ r.expr rhs = some r' ∧
      r.expr type = some t ∧ lhs' = VExpr.wrapLams domains' l ∧
      rhs' = VExpr.wrapLams domains' r' ∧ type' = VExpr.wrapForalls domains' t ∧
      domains'.length = domains.length := by
  induction domains generalizing lhs' rhs' type' with
  | nil => exact ⟨[], lhs', rhs', type', hl, hr, ht, rfl, rfl, rfl, rfl⟩
  | cons d ds ih =>
    obtain ⟨dl, l, hdl, hlBody, rfl⟩ := Restoration.expr_lam_parts hl
    obtain ⟨dr, rr, hdr, hrBody, rfl⟩ := Restoration.expr_lam_parts hr
    have hd : dr = dl := Option.some.inj (hdr.symm.trans hdl)
    subst dr
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds type)
               pure (.forallE d' t')) = some type' at ht
    simp only [bind, Option.bind_eq_some_iff] at ht
    obtain ⟨dt, hdt, t, ht, heq⟩ := ht
    have hd : dt = dl := Option.some.inj (hdt.symm.trans hdl)
    subst dt
    cases heq
    obtain ⟨ds', l', r', t', hl', hr', ht', rfl, rfl, rfl, hlen⟩ := ih hlBody hrBody ht
    exact ⟨dl :: ds', l', r', t', hl', hr', ht', rfl, rfl, rfl, by simpa using hlen⟩

theorem restoration_mkApps (r : Restoration) (fn : VExpr)
    (inputArgs args : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps fn inputArgs) args = (do
      let restoredArgs ← inputArgs.mapM r.expr
      Restoration.expr.go r fn (restoredArgs ++ args)) := by
  induction inputArgs generalizing fn with
  | nil => rfl
  | cons a as ih =>
    change Restoration.expr.go r (VExpr.mkApps (.app fn a) as) args = _
    rw [ih]
    cases ha : r.expr a <;> cases has : as.mapM r.expr <;>
      simp only [Restoration.expr] at ha <;>
      simp [List.mapM_cons, has, Restoration.expr.go, Restoration.expr, ha]

private theorem restoration_vars (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  unfold vars
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih => simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using ih

theorem spine_mkApps_exact (fn : VExpr) (args : List VExpr)
    (h : fn.getAppFnArgs = (fn, [])) :
    (VExpr.mkApps fn args).getAppFnArgs = (fn, args) := by
  have go : ∀ e args, VExpr.getAppFnArgs.go e args =
      (e.getAppFnArgs.1, e.getAppFnArgs.2 ++ args) := by
    intro e
    induction e with
    | app f a ih _ =>
      intro args
      change VExpr.getAppFnArgs.go f (a :: args) = _
      rw [ih]
      change _ = ((VExpr.getAppFnArgs.go f [a]).1, (VExpr.getAppFnArgs.go f [a]).2 ++ args)
      rw [ih]
      simp
    | _ => intros; rfl
  have apps : ∀ fn args acc, VExpr.getAppFnArgs.go (VExpr.mkApps fn args) acc =
      VExpr.getAppFnArgs.go fn (args ++ acc) := by
    intro fn args
    induction args generalizing fn with
    | nil => intros; rfl
    | cons a as ih => intro acc; exact ih (.app fn a) acc
  change VExpr.getAppFnArgs.go (VExpr.mkApps fn args) [] = _
  rw [apps, List.append_nil, go, h]
  rfl

private theorem restored_constructor_arguments {r : Restoration}
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ np)
    {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np offset ++ vars nf 0)) = some output) :
    ∃ name' levels' params', output.getAppFnArgs =
      (.const name' levels', params' ++ vars nf 0) := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) _) [] = _ at h
  rw [restoration_mkApps] at h
  simp [List.mapM_append, restoration_vars] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hspec
    have hle := hparams spec (List.mem_of_find?_eq_some hspec)
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · cases h
      rw [spine_mkApps_exact _ _ rfl]
      rw [List.drop_append_of_le_length (by simpa [vars] using hle), ← List.append_assoc]
      exact ⟨_, _, _, rfl⟩
  · cases h
    rw [spine_mkApps_exact _ _ rfl]
    exact ⟨_, _, _, rfl⟩


namespace CaseSchema

theorem extract_wrap {lhs rhs type : VExpr}
    (hhead : lhs.getAppFnArgs.1 = .elim block owner levels) (domains : List VExpr) :
    EquationBody.extract (VExpr.wrapLams domains lhs) (VExpr.wrapLams domains rhs)
      (VExpr.wrapForalls domains type) = some ⟨domains, lhs, rhs, type⟩ := by
  induction domains with
  | nil => cases lhs <;> first | rfl | cases hhead
  | cons d ds ih =>
    change (do
      if d ≠ d ∨ d ≠ d then none else
      let body ← EquationBody.extract (VExpr.wrapLams ds lhs) (VExpr.wrapLams ds rhs)
        (VExpr.wrapForalls ds type)
      pure { body with domains := d :: body.domains }) = _
    simp [ih]

private theorem application_extract_of_heads {fn major : VExpr}
    (hf : fn.getAppFnArgs.1 = .elim block owner levels)
    (hm : major.getAppFnArgs.1 = .const ctor ctorLevels) :
    ∃ application, Application.extract (.app fn major) = some application ∧
      application.block = block ∧ application.owner = owner := by
  cases hfn : fn.getAppFnArgs with
  | mk head args =>
    simp only [hfn] at hf
    cases hf
    cases hmajor : major.getAppFnArgs with
    | mk head ctorArgs =>
      simp only [hmajor] at hm
      cases hm
      exact ⟨⟨block, owner, levels, args, ctor, ctorLevels, ctorArgs⟩,
        by simp [Application.extract, hfn, hmajor], rfl, rfl⟩

private theorem extract_restored_rule {r : Restoration} {domains : List VExpr}
    {fn major rhs type : VExpr} {equation : VDefEq}
    (hf : fn.getAppFnArgs.1 = .elim block owner levels)
    (hm : major.getAppFnArgs.1 = .const ctor ctorLevels)
    (hl : r.expr (VExpr.wrapLams domains (.app fn major)) = some equation.lhs)
    (hr : r.expr (VExpr.wrapLams domains rhs) = some equation.rhs)
    (ht : r.expr (VExpr.wrapForalls domains type) = some equation.type) :
    ∃ rule, AppliedRule.extract block owner equation = some rule := by
  obtain ⟨domains', lhs', rhs', type', hl', _, _, hel, her, het, _⟩ :=
    restored_common_telescope hl hr ht
  change (do let major' ← r.expr major; Restoration.expr.go r fn [major']) = some lhs' at hl'
  simp only [bind, Option.bind_eq_some_iff] at hl'
  obtain ⟨major', hmajor, hfn⟩ := hl'
  obtain ⟨ctor', ctorLevels', hmajorHead⟩ := restored_const_head hm hmajor
  obtain ⟨preArgs, heq⟩ := restored_elim_spine hf hfn
  have hlhs : lhs' = .app (VExpr.mkApps (.elim block owner levels) preArgs) major' := by
    simpa [VExpr.mkApps, List.foldl_append] using heq
  obtain ⟨application, ha, hb, ho⟩ := application_extract_of_heads
    (VExpr.reduction_head_mkApps (.elim block owner levels) preArgs) hmajorHead
  rw [← hlhs] at ha
  have hhead : lhs'.getAppFnArgs.1 = .elim block owner levels := by
    rw [hlhs, VExpr.reduction_head_app]
    exact VExpr.reduction_head_mkApps _ _
  have hbody : EquationBody.extract equation.lhs equation.rhs equation.type =
      some ⟨domains', lhs', rhs', type'⟩ := by
    rw [hel, her, het]
    exact extract_wrap hhead domains'
  exact ⟨⟨equation, ⟨domains', lhs', rhs', type'⟩, application⟩, by
    simp [AppliedRule.extract, hbody, ha, hb, ho]⟩

/-- Successful restoration of a generated case equation always leaves an
extractable applied rule, with its own block and family slot. -/
theorem extract_of_genericEquation {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericEquations block owner = some rules) (hmem : equation ∈ rules) :
    ∃ rule, AppliedRule.extract block owner.val equation = some rule := by
  obtain ⟨index, hrestore⟩ := equation_of_mem h hmem
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra ctor.fields.length
  let args := vars ((schema.view owner).params.length + extra) ctor.fields.length ++ indices
  refine extract_restored_rule
    (levels := g.targetLevel :: g.levels) (ctor := ctor.name) (ctorLevels := g.levels)
    (fn := VExpr.mkApps (g.recursorHead (.elim block owner.val) ctor.owner) args)
    (major := g.constructorApp ctor extra 0) ?_ ?_ ?_ hr ht
  · rw [VExpr.reduction_head_mkApps]
    simp [Instance.recursorHead, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go]
  · exact VExpr.reduction_head_mkApps _ _
  · simpa only [Instance.equation, g, ctor, extra, indices, args, VExpr.mkApps,
      List.foldl_append, List.foldl_cons, List.foldl_nil] using hl

/-- Every generic generated equation is generated in the sense of the applied
case-rule relation (`Generates`); parsing adds no caller-supplied equations or assumptions. -/
theorem generates_of_genericEquation {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericEquations block owner = some rules) (hmem : equation ∈ rules) :
    ∃ rule, schema.Generates block owner rule ∧ rule.equation = equation := by
  obtain ⟨rule, he⟩ := extract_of_genericEquation h hmem
  have heq := (AppliedRule.extract_spec he).1
  exact ⟨rule, ⟨rules, h, heq ▸ hmem, heq ▸ he⟩, heq⟩

private theorem view_constructor_external {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (index : Fin (schema.view owner).constructors.size) :
    Instance.recursiveFields (schema.view owner).constructors[index] = [] := by
  obtain ⟨ctor, _, _, hc⟩ := view_constructor_eq_caseConstructor index
  rw [hc]
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  obtain ⟨domain, _, hd⟩ := List.mem_map.mp hfield
  cases field with
  | external => rfl
  | recursive => cases hd

/-- Case computation applies the selected minor only to its constructor fields;
there are no recursive induction hypotheses in the case-view generator. -/
theorem Generates.rhs_shape {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hgen : schema.Generates block owner rule) :
    ∃ minor nf, rule.body.rhs = VExpr.mkApps (.bvar minor) (vars nf 0) := by
  obtain ⟨rules, hg, hm, he⟩ := hgen
  obtain ⟨index, hrestore⟩ := equation_of_mem hg hm
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨ds, lhs, rhs, type, hl', hr', _, hel, her, het, _⟩ :=
    restored_common_telescope hl hr ht
  have hnoRec := view_constructor_external (schema := schema) (owner := owner) index
  let ctor := (schema.view owner).constructors[index]
  have hrhs : rhs = VExpr.mkApps
      (.bvar (ctor.fields.length + (schema.view owner).constructors.size - 1 - index.val))
      (vars ctor.fields.length 0) := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some rhs at hr'
    simp only [hnoRec, List.map_nil, List.append_nil] at hr'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hr'
    rw [restoration_mkApps] at hr'
    simp [restoration_vars, Restoration.expr.go] at hr'
    exact hr'.symm
  have hhead := Restoration.go_head_elim
    (hhead := VExpr.reduction_head_mkApps _ _) hl'
  have hb := extract_wrap (rhs := rhs) (type := type) hhead ds
  rw [← hel, ← her, ← het] at hb
  have hbody := Option.some.inj (hb.symm.trans (AppliedRule.extract_spec he).2.1)
  rw [← hbody]
  exact ⟨_, _, hrhs⟩

private theorem vars_join (p f : Nat) : vars p f ++ vars f 0 = vars (p + f) 0 := by
  rw [Nat.add_comm p f]
  simp [vars, List.range_add, List.reverse_append, List.map_append, List.map_map]

/-- The generated body's designated prefix and constructor-field occurrences
recover its entire binder telescope. Restoration may specialize constructor
parameters, but never consumes any of the following fields. -/
theorem Generates.capture_shape {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hgen : schema.Generates block owner rule) :
    ∃ index : Fin (schema.view owner).constructors.size,
      rule.capture rule.application = vars rule.body.domains.length 0 ∧
      rule.application.arguments.length = schema.signature.params.length + 1 +
        (schema.view owner).constructors.size +
        (schema.view owner).constructors[index].indices.length := by
  obtain ⟨rules, hg, hm, he⟩ := hgen
  obtain ⟨index, hrestore⟩ := equation_of_mem hg hm
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders (((schema.view owner).fieldTypes ctor).map (·.instL g.levels)) extra
  let major := g.constructorApp ctor extra 0
  have hnoRec := view_constructor_external (schema := schema) (owner := owner) index
  have hdomlen : domains.length = np + nf := by
    simp only [domains, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList]
    simp only [np, nf, extra]
    omega
  obtain ⟨ds', lhs', rhs', type', hl', hr', _, hel, her, het, hlen⟩ :=
    restored_common_telescope hl hr ht
  have hlen' : ds'.length = np + nf := hlen.trans hdomlen
  have hrhs : rhs' = VExpr.mkApps (.bvar (nf + (schema.view owner).constructors.size - 1 - index.val))
      (vars nf 0) := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some rhs' at hr'
    simp only [hnoRec, List.map_nil, List.append_nil] at hr'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hr'
    rw [restoration_mkApps] at hr'
    simp [restoration_vars, Restoration.expr.go] at hr'
    exact hr'.symm
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  have hlhs0 : schema.restoration.expr
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices ++ [major])) = some lhs' := by
    simpa only [Instance.recursorHead, hzero, Nat.add_zero] using hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp [List.mapM_append, restoration_vars, List.mapM_cons, Restoration.expr.go] at hlhs0
  obtain ⟨allArgs, ⟨restArgs, ⟨indices', hi, majorArgs, ⟨major', hmajor, rfl⟩, rfl⟩, rfl⟩, hout⟩ := hlhs0
  have hlhs : lhs' = .app
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices')) major' := by
    simpa [VExpr.mkApps, List.foldl_append] using hout.symm
  have hmParams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ (schema.view owner).params.length := hparams
  obtain ⟨cn, cl, cp, hc⟩ := restored_constructor_arguments hmParams hmajor
  have ha : Application.extract lhs' = some
      ⟨block, owner.val, g.targetLevel :: g.levels, vars np nf ++ indices', cn, cl, cp ++ vars nf 0⟩ := by
    rw [hlhs]
    simp only [Application.extract,
      spine_mkApps_exact (.elim block owner.val (g.targetLevel :: g.levels)) _ rfl, hc]
    rfl
  have hhead : lhs'.getAppFnArgs.1 = .elim block owner.val (g.targetLevel :: g.levels) := by
    rw [hlhs, VExpr.reduction_head_app]
    exact VExpr.reduction_head_mkApps _ _
  have hb := extract_wrap (rhs := rhs') (type := type') hhead ds'
  rw [← hel, ← her, ← het] at hb
  simp [AppliedRule.extract, hb, ha] at he
  refine ⟨index, ?_, ?_⟩
  · rw [← he]
    simp only [AppliedRule.capture, AppliedRule.numPrefix, AppliedRule.numFields]
    rw [hrhs, spine_mkApps_exact _ _ rfl]
    simp only [vars, List.length_map, List.length_reverse, List.length_range] at hlen' ⊢
    change (vars np nf ++ indices').take (ds'.length - nf) ++
      (cp ++ vars nf 0).drop ((cp ++ vars nf 0).length - nf) = vars ds'.length 0
    rw [hlen']
    simp only [Nat.add_sub_cancel]
    have hpLen : (vars np nf).length = np := by simp [vars]
    have hfLen : (vars nf 0).length = nf := by simp [vars]
    rw [List.take_left' hpLen, List.length_append, hfLen, Nat.add_sub_cancel,
      List.drop_left]
    exact vars_join np nf
  · have hidx : indices'.length = indices.length := by
      have length_eq : ∀ {xs ys}, List.Forall₂ (fun x y => schema.restoration.expr x = some y) xs ys →
          ys.length = xs.length := by
        intro xs ys hrel
        induction hrel with
        | nil => rfl
        | cons _ _ ih => simp [ih]
      exact length_eq (List.mapM_eq_some.mp hi)
    rw [← he]
    change (vars np nf ++ indices').length = _
    rw [List.length_append, hidx]
    simp only [vars, List.length_map, List.length_reverse, List.length_range,
      indices, np, extra, view_familyCount, Nat.add_assoc]
    rfl

/-- Capture recovers the complete binder telescope of a generated case rule. -/
theorem Generates.capture_template {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hgen : schema.Generates block owner rule) :
    rule.capture rule.application = vars rule.body.domains.length 0 := by
  obtain ⟨_, hc, _⟩ := hgen.capture_shape hparams
  exact hc

/-- Rules for a selected family have its fixed generated argument arity. -/
theorem Generates.arguments_length {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hindices : ∀ index : Fin (schema.view owner).constructors.size,
      (schema.view owner).constructors[index].indices.length =
        schema.signature.families[owner].indices.length)
    (hgen : schema.Generates block owner rule) :
    rule.application.arguments.length = schema.signature.params.length + 1 +
      (schema.view owner).constructors.size + schema.signature.families[owner].indices.length := by
  obtain ⟨index, _, ha⟩ := hgen.capture_shape hparams
  rw [ha, hindices index]


private theorem capture_map_specialization (rule : AppliedRule) (a : Application)
    (levels : List VLevel) (arguments : List VExpr) :
    rule.capture (a.specialize levels arguments) =
      (rule.capture a).map (fun e => instantiateParams (e.instL levels) arguments) := by
  simp [AppliedRule.capture, Application.specialize, List.map_take, List.map_drop, List.map_append]

private theorem instantiate_vars (arguments : List VExpr) (levels : List VLevel) :
    (vars arguments.length 0).map (fun e => instantiateParams (e.instL levels) arguments) = arguments := by
  apply List.ext_getElem
  · simp [vars]
  · intro i hi hi'
    have hj : arguments.length - 1 - i < arguments.length := by omega
    have heq : arguments.length - 1 - (arguments.length - 1 - i) = i := by omega
    simp [vars, List.getElem_reverse, instantiateParams, VExpr.instL, VExpr.subst, hj, heq]

/-- Universe and simultaneous term specialization preserve the
capture positions, recovering the exact actual argument list. -/
theorem Generates.capture_specialize {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hgen : schema.Generates block owner rule)
    (hlen : arguments.length = rule.body.domains.length) :
    rule.capture (rule.application.specialize levels arguments) = arguments := by
  rw [capture_map_specialization, hgen.capture_template hparams, ← hlen]
  exact instantiate_vars arguments levels

/-- The parsed abstract head retains the complete generic universe spine. -/
theorem Generates.application_levels {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hgen : schema.Generates block owner rule) :
    rule.application.levels = VLevel.params schema.genericUvars := by
  obtain ⟨rules, hg, hm, he⟩ := hgen
  have hh := genericEquation_head hg hm
  have hb := EquationBody.extract_sound (AppliedRule.extract_spec he).2.1
  have ha := Application.extract_sound (AppliedRule.extract_spec he).2.2.1
  rw [← ha] at hb
  have hs : (VExpr.wrapLams rule.body.domains rule.application.expr).stripLams =
      rule.application.expr := by
    induction rule.body.domains with
    | nil => rfl
    | cons _ _ ih => exact ih
  rw [← hb.1, hs, Application.head] at hh
  have hlevels := (VExpr.elim.inj hh).2.2
  rw [hlevels]
  simp [genericUvars, genericLevels, VLevel.params, List.range_succ_eq_map,
    List.map_map, Function.comp_def]

/-- Restoration preserves the generic equation's declared universe arity. -/
theorem Generates.equation_uvars {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hgen : schema.Generates block owner rule) :
    rule.equation.uvars = schema.genericUvars := by
  obtain ⟨rules, hg, hm, _⟩ := hgen
  obtain ⟨index, he⟩ := equation_of_mem hg hm
  simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at he
  obtain ⟨lhs, _, rhs, _, type, _, he⟩ := he
  exact (congrArg VDefEq.uvars (Option.some.inj he)).symm

/-- Instantiating the generated abstract universe spine recovers the supplied
universe list at precisely the equation's declared arity. -/
theorem Generates.application_levels_inst {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hgen : schema.Generates block owner rule)
    (hlen : levels.length = rule.equation.uvars) :
    rule.application.levels.map (·.inst levels) = levels := by
  rw [hgen.application_levels]
  exact VLevel.inst_map_id (hlen.trans hgen.equation_uvars)

end CaseSchema
end InductiveSignature
end Lean4Lean
