import Lean4Lean.Theory.Typing.PatsIota
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Typing.SignatureVars

/-! # The compiled block behind a registered ι pattern

Every registered pattern of a well-formed environment is the ι entry of a recursor rule of an
installed declaration (`VEnv.WF'.pats_origin`), whose recursors and rules are read off a finite
compilation (`VInductDecl.RecsCompiled`, `CompiledInductive`). This file extracts the
compilation data behind a `CompiledInductive` derivation (`CompiledInductive.data`), computes
the syntax of the generated equations of an *ordinary* compilation (one without container
specializations, `auxiliaries = []`: `Instance.equation_lhs_eq`, `equation_rhs_eq`, the
inversion `VRecRule.OfEquation.ordinary` of a model rule against its generated equation), and
proves that the reduct template of an ordinary rule mentions only constants of the recursor's
type and the block's recursor names (`Instance.equation_rhs_containsAnyConst`). -/

namespace Lean4Lean

/-! ## The data of a compilation -/

/-- A finite compilation derivation is a `CompilationData` at some base environment below the
ambient one (peeling the `replay` steps). -/
theorem CompiledInductive.data {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : CompiledInductive env decl block) :
    ∃ (base : VEnv) (expanded : VInductDecl) (s : InductiveSignature)
      (g : InductiveSignature.Instance s) (aux : List InductiveSignature.ContainerSpecialization),
      base ≤ env ∧ InductiveSignature.CompilationData base decl expanded s g aux block ∧
        ContainersInstalled base aux := by
  induction H using CompiledInductive.rec (motive_2 := fun _ _ _ => True) with
  | intro h hc _ => exact ⟨_, _, _, _, _, .rfl, h, hc⟩
  | replay _ hle _ ih =>
    obtain ⟨b, e, s, g, a, h1, h2, h3⟩ := ih
    exact ⟨b, e, s, g, a, h1.trans hle, h2, h3⟩
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ => trivial

namespace InductiveSignature

theorem compilationRestoration_nil (source : VInductDecl) :
    compilationRestoration source [] = {} := rfl

/-- The rules of an ordinary compilation are the generated equations. -/
theorem CompilationData.ordinary_rules {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) : block.rules = g.equations := by
  have := H.equations
  rw [compilationRestoration_nil, Instance.restoredEquations_empty] at this
  exact (Option.some.inj this).symm

/-- The recursors of an ordinary compilation are the generated recursors. -/
theorem CompilationData.ordinary_recursors {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) : block.recursors = g.recursors := by
  have := H.recursors
  rw [compilationRestoration_nil, Instance.restoredRecursors_empty] at this
  exact (Option.some.inj this).symm

/-! ## Syntax of the generated equations -/

/-- The parameters of the major of a generated equation. -/
def eqMs {s : InductiveSignature} (index : Fin s.constructors.size) : List VExpr :=
  vars s.params.length ((s.families.size + s.constructors.size) +
    s.constructors[index].fields.length + 0)

/-- The field variables of the major of a generated equation. -/
def eqFs {s : InductiveSignature} (index : Fin s.constructors.size) : List Nat :=
  (List.range s.constructors[index].fields.length).reverse

namespace Instance

variable {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size)

/-- The binder domains of the generated equation of a constructor. -/
def eqDoms : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size)

/-- The constructor's indices in the generated equation. -/
def eqIndices : List VExpr :=
  s.constructors[index].indices.map fun e =>
    (e.instL g.levels).liftN (s.families.size + s.constructors.size)
      s.constructors[index].fields.length

/-- The leading arguments (parameters, motives, minors, indices) of the generated
equation. -/
def eqLead : List VExpr :=
  vars (s.params.length + (s.families.size + s.constructors.size))
    s.constructors[index].fields.length ++ g.eqIndices index

/-- The recursive calls of the generated equation. -/
def eqCalls : List VExpr :=
  (recursiveFields s.constructors[index]).map fun (field, r) =>
    g.recursiveCall s.constructors[index] field r

/-- The body of the reduct of the generated equation. -/
def eqBody : VExpr :=
  VExpr.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size - 1 - index.val))
    (vars s.constructors[index].fields.length 0 ++ g.eqCalls index)

theorem params_length : g.params.length = s.params.length := by simp [Instance.params]
theorem motives_length : g.motives.length = s.families.size := by simp [Instance.motives]
theorem minors_length : g.minors.length = s.constructors.size := by simp [Instance.minors]

theorem eqDoms_length : (g.eqDoms index).length =
    s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].fields.length := by
  simp only [eqDoms, Instance.params, Instance.motives, Instance.minors,
    insertBinders, fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
    Array.length_toList]
  omega

theorem eqIndices_length : (g.eqIndices index).length = s.constructors[index].indices.length := by
  simp [eqIndices]

theorem eqLead_length : (g.eqLead index).length =
    s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length := by
  simp [eqLead, eqIndices, length_vars]

theorem equation_lhs_eq : (g.equation index).lhs = .wrapLams (g.eqDoms index)
    (.mkApps (.const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars))
      (g.eqLead index ++ [.mkApps (.const s.constructors[index].name g.levels)
        (eqMs index ++ (eqFs index).map .bvar)])) := by
  simp only [equation, constructorApp, recursorHead, eqDoms, eqLead, eqMs, eqFs, eqIndices,
    vars_zero, List.append_assoc]

theorem equation_rhs_eq : (g.equation index).rhs = .wrapLams (g.eqDoms index) (g.eqBody index) :=
  rfl

theorem equation_uvars : (g.equation index).uvars = g.uvars := rfl

theorem eqMs_length : (eqMs index).length = s.params.length := by simp [eqMs, length_vars]
theorem eqFs_length : (eqFs index).length = s.constructors[index].fields.length := by simp [eqFs]

/-- Every binder of a generated equation is a bare leading argument or a field. -/
theorem equation_cov : ∀ x < (g.eqDoms index).length,
    VExpr.bvar x ∈ g.eqLead index ∨ x ∈ eqFs index := by
  intro x hx
  rw [eqDoms_length] at hx
  by_cases hxf : x < s.constructors[index].fields.length
  · exact .inr (by simpa [eqFs] using hxf)
  · exact .inl (List.mem_append_left _ (mem_vars (by omega) (by omega)))

/-- The binder domains of the generated recursor's type. -/
def recDoms (owner : Fin s.families.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size) ++
    [g.familyApp owner (vars s.params.length ((s.families.size + s.constructors.size) +
      s.families[owner].indices.length)) (vars s.families[owner].indices.length 0)]

/-- The body of the generated recursor's type. -/
def recBody (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps (.bvar ((insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)).length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val)))
    (vars (insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)).length 1 ++ [.bvar 0])

theorem recursorType_eq_recDoms (owner : Fin s.families.size) :
    (g.recursor owner).type = .wrapForalls (g.recDoms owner) (g.recBody owner) := by
  simp only [recursor, recursorType, recDoms, recBody, Instance.familyApp, insertBinders,
    List.length_map, List.length_zipIdx]

theorem recDoms_length (owner : Fin s.families.size) :
    (g.recDoms owner).length = s.params.length + (s.families.size + s.constructors.size) +
      s.families[owner].indices.length + 1 := by
  simp only [recDoms, Instance.params, Instance.motives, Instance.minors,
    insertBinders, List.length_append, List.length_map, List.length_zipIdx,
    Array.length_toList, List.length_singleton]
  omega

theorem recDoms_major (owner : Fin s.families.size) :
    (g.recDoms owner)[s.params.length + (s.families.size + s.constructors.size) +
      s.families[owner].indices.length]? =
    some (.mkApps (.const s.families[owner].name g.levels)
      (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[owner].indices.length) ++ vars s.families[owner].indices.length 0)) := by
  have hl := g.recDoms_length owner
  rw [List.getElem?_eq_getElem (by omega)]
  simp only [recDoms] at hl ⊢
  rw [List.getElem_append_right (by simp at hl ⊢; omega)]
  simp only [Option.some.injEq]
  have : s.params.length + (s.families.size + s.constructors.size) +
      s.families[owner].indices.length -
      (g.params ++ g.motives ++ g.minors ++ insertBinders
        (s.families[owner].indices.map (·.instL g.levels))
        (s.families.size + s.constructors.size)).length = 0 := by
    simp only [Instance.params, Instance.motives, Instance.minors,
      insertBinders, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList]
    omega
  simp only [this, List.getElem_singleton]
  rfl

/-- The recursor telescope and the equation telescope share the parameters, motives and
minors. -/
theorem recDoms_take (owner : Fin s.families.size) :
    (g.recDoms owner).take (s.params.length + (s.families.size + s.constructors.size)) =
      g.params ++ g.motives ++ g.minors := by
  have hl : (g.params ++ g.motives ++ g.minors).length =
      s.params.length + (s.families.size + s.constructors.size) := by
    simp only [List.length_append, params_length, motives_length, minors_length]; omega
  rw [show g.recDoms owner = (g.params ++ g.motives ++ g.minors) ++
    (insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size) ++
    [g.familyApp owner (vars s.params.length ((s.families.size + s.constructors.size) +
      s.families[owner].indices.length)) (vars s.families[owner].indices.length 0)]) by
    simp only [recDoms, List.append_assoc]]
  rw [← hl, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

theorem eqDoms_take :
    (g.eqDoms index).take (s.params.length + (s.families.size + s.constructors.size)) =
      g.params ++ g.motives ++ g.minors := by
  have hl : (g.params ++ g.motives ++ g.minors).length =
      s.params.length + (s.families.size + s.constructors.size) := by
    simp only [List.length_append, params_length, motives_length, minors_length]; omega
  simp only [eqDoms]
  rw [← hl, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

theorem recursor_mem (owner : Fin s.families.size) : g.recursor owner ∈ g.recursors :=
  List.mem_map.2 ⟨owner, List.mem_finRange _, rfl⟩

theorem equation_mem : g.equation index ∈ g.equations :=
  List.mem_map.2 ⟨index, List.mem_finRange _, rfl⟩

theorem minor_mem : g.minor s.constructors[index] index.val ∈ g.minors := by
  simp only [Instance.minors, List.mem_map]
  refine ⟨(s.constructors[index], index.val), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨index.val, by simp, by simp⟩

end Instance

/-! ## Inverting a model rule against its generated equation -/

theorem _root_.Lean4Lean.VExpr.lamBody_mkApps_const (c : Name) (ls : List VLevel)
    (args : List VExpr) :
    (VExpr.mkApps (.const c ls) args).lamBody = VExpr.mkApps (.const c ls) args := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, VExpr.mkApps_snoc]; rfl

/-- The data of a model rule read off a generated equation of an ordinary compilation: its
recursor name, major index, constructor, field count and reduct. -/
theorem VRecRule.OfEquation.ordinary {s : InductiveSignature} {g : Instance s}
    {r : VRecursor} {ru : VRecRule} {index : Fin s.constructors.size}
    (H : VRecRule.OfEquation r ru (g.equation index)) :
    r.name = g.recursorName s.constructors[index].owner ∧
    r.getMajorIdx = s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length ∧
    ru.ctor = s.constructors[index].name ∧
    ru.ctorParams + ru.nfields = s.params.length + s.constructors[index].fields.length ∧
    ru.rhs = (g.equation index).rhs := by
  obtain ⟨hrhs, hhead, hlen, major, hmajor, hmc, hml⟩ := H
  rw [g.equation_lhs_eq, VExpr.lamBody_wrapLams, VExpr.lamBody_mkApps_const] at hhead hlen hmajor
  have hfn : ∀ args, (VExpr.mkApps (.const (g.recursorName s.constructors[index].owner)
      (VLevel.params g.uvars)) args).getAppFn =
      .const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars) := by
    intro args; simp [VExpr.getAppFn]
  rw [VExpr.headConst?_eq_some] at hhead
  obtain ⟨us, hus⟩ := hhead
  rw [hfn] at hus
  rw [VExpr.getAppArgs_mkApps] at hlen hmajor
  simp only [VExpr.getAppArgs, List.nil_append, List.length_append, List.length_singleton,
    Instance.eqLead_length] at hlen
  simp only [VExpr.getAppArgs, List.nil_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hmajor
  subst hmajor
  rw [VExpr.headConst?_eq_some] at hmc
  obtain ⟨us', hus'⟩ := hmc
  rw [VExpr.getAppFn_mkApps] at hus'
  simp only [VExpr.getAppFn, VExpr.const.injEq] at hus'
  rw [VExpr.getAppArgs_mkApps] at hml
  simp only [VExpr.getAppArgs, List.nil_append, List.length_append, List.length_map,
    Instance.eqMs_length, Instance.eqFs_length] at hml
  refine ⟨(VExpr.const.inj hus).1.symm, by omega, hus'.1.symm, hml.symm, hrhs.symm⟩

end InductiveSignature

/-! ## Instances of ι patterns -/

/-- Inversion of a match against a constructor spine pattern `(.const c).varN n`: the matched
expression is `c` applied to `n` arguments, the holes holding the arguments. -/
theorem Pattern.matches_varN_const_inv {c : Name} : ∀ {n : Nat} {e : VExpr} {m1 : List VLevel}
    {g : ((Pattern.const c).varN n).Path → VExpr}, ((Pattern.const c).varN n).Matches e m1 g →
    ∃ (args : List VExpr) (hlen : args.length = n), e = (VExpr.const c m1).mkApps args ∧
      ∀ i (hi : i < n), g (Pattern.varN_pathOf n i hi) = args[i]'(hlen ▸ hi)
  | 0, e, m1, g, h => by
    cases h; exact ⟨[], rfl, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | n+1, e, m1, g, h => by
    simp only [Pattern.varN] at h
    cases h with
    | @var f f' f1 g1 a' h =>
      obtain ⟨args, hlen, rfl, hg⟩ := Pattern.matches_varN_const_inv h
      refine ⟨args ++ [a'], by simp [hlen], by rw [VExpr.mkApps_append]; rfl, fun i hi => ?_⟩
      have key : (Pattern.varN_pathOf (q := Pattern.const c) (n+1) i hi :
          Option ((Pattern.const c).varN n).Path) =
          if hik : i = n then none else some (Pattern.varN_pathOf n i (by omega)) := rfl
      show Option.elim (Pattern.varN_pathOf (q := Pattern.const c) (n+1) i hi :
          Option ((Pattern.const c).varN n).Path) a' g1 = _
      rw [key]
      by_cases hik : i = n
      · subst hik; rw [dif_pos rfl]; simp [hlen]
      · rw [dif_neg hik, Option.elim, hg i (by omega), List.getElem_append_left (by omega)]

/-- Inversion of a match against an ι pattern: the recursor applied to `M` arguments, the last
of which is the constructor applied to `N` arguments. -/
theorem SimplePattern.iota_matches_inv {r c : Name} {M N : Nat} {e : VExpr} {m1 : List VLevel}
    {m2 : (SimplePattern.iota r M c N).toPattern.Path → VExpr}
    (h : (SimplePattern.iota r M c N).toPattern.Matches e m1 m2) :
    ∃ (recArgs ctorArgs : List VExpr) (lsC : List VLevel) (h1 : recArgs.length = M)
      (h2 : ctorArgs.length = N),
      e = (VExpr.const r m1).mkApps (recArgs ++ [(VExpr.const c lsC).mkApps ctorArgs]) ∧
      (∀ i (hi : i < M), m2 (Sum.inl (Pattern.varN_pathOf M i hi)) = recArgs[i]'(h1 ▸ hi)) ∧
      (∀ i (hi : i < N), m2 (Sum.inr (Pattern.varN_pathOf N i hi)) = ctorArgs[i]'(h2 ▸ hi)) := by
  simp only [SimplePattern.toPattern] at h
  cases h with
  | @app f f' f1 g1 a a' f2 g2 h1 h2 =>
    obtain ⟨recArgs, hl1, rfl, hg1⟩ := Pattern.matches_varN_const_inv h1
    obtain ⟨ctorArgs, hl2, rfl, hg2⟩ := Pattern.matches_varN_const_inv h2
    exact ⟨recArgs, ctorArgs, f2, hl1, hl2, by rw [VExpr.mkApps_append]; rfl,
      fun i hi => hg1 i hi, fun i hi => hg2 i hi⟩

/-- The reduct of an instance of an ι rule: the template, level-instantiated, applied to the
recursor's first `k` arguments and the constructor's last `nf` arguments. -/
theorem SimplePattern.iotaRHS_apply_of_matches {r c : Name} {k nind cnp nf : Nat} {rhs : VExpr}
    {hc : rhs.Closed} {e : VExpr} {m1 : List VLevel}
    {m2 : (SimplePattern.iota r (k + nind) c (cnp + nf)).toPattern.Path → VExpr}
    (h : (SimplePattern.iota r (k + nind) c (cnp + nf)).toPattern.Matches e m1 m2) :
    ∃ (recArgs ctorArgs : List VExpr) (lsC : List VLevel), recArgs.length = k + nind ∧
      ctorArgs.length = cnp + nf ∧
      e = (VExpr.const r m1).mkApps (recArgs ++ [(VExpr.const c lsC).mkApps ctorArgs]) ∧
      (SimplePattern.iotaRHS' r c k nind cnp nf rhs hc).apply m1 m2 =
        (rhs.instL m1).mkApps (recArgs.take k ++ ctorArgs.drop cnp) := by
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, hg1, hg2⟩ := SimplePattern.iota_matches_inv h
  exact ⟨recArgs, ctorArgs, lsC, h1, h2, rfl,
    SimplePattern.iotaRHS'_apply r c k nind cnp nf rhs hc m1 m2 h1 h2 hg1 hg2⟩

/-! ## The block behind a rule -/

/-- The recursor stage of a compiled block is the recursor stage of its declaration: the block
lays out the declaration's type formers, constructors and projection entries
(`CompilesTo`), and its recursors are the declaration's (`RecsOf`). -/
theorem VInductDecl.recursorStage_eq {env envT envC envRec envR : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (hcomp : decl.CompilesTo env block) (hrecsOf : decl.RecsOf block)
    (hT : env.addConstVals block.types = some envT)
    (hC : envT.addConstVals block.ctors = some envC)
    (hRec : (envC.addProjections block.projections).addConstVals block.recursors = some envRec)
    (hR : decl.addTypesCtorsProjsRecs env = some envR) : envRec = envR := by
  have hT' : decl.addTypes env = some envT := by
    rw [VInductDecl.addTypes_eq_addConstVals, ← hcomp.types]; exact hT
  have hC' : decl.addCtors envT = some envC := by
    rw [VInductDecl.addCtors_eq_addConstVals, ← hcomp.ctors]; exact hC
  have hRec' : decl.addRecs (decl.addProjs envC) = some envRec := by
    rw [VInductDecl.addRecs_eq_addConstVals, hrecsOf.recursors]
    show (envC.addProjections decl.projectionEntries).addConstVals block.recursors = some envRec
    rw [← hcomp.projections]; exact hRec
  unfold VInductDecl.addTypesCtorsProjsRecs VInductDecl.addTypesCtorsProjs
    VInductDecl.addTypesCtors at hR
  rw [hT'] at hR
  have h1 : Option.map decl.addProjs (decl.addCtors envT) >>= decl.addRecs = some envR := hR
  rw [hC'] at h1
  have h2 : decl.addRecs (decl.addProjs envC) = some envR := h1
  rw [hRec'] at h2
  exact Option.some.inj h2

/-- The equations of the compiled block of a well-formed declaration are typed in the
declaration's recursor stage (`VInductBlock.WF`, read through `VInductDecl.RecsCompiled`). -/
theorem VInductDecl.WF.block_rules_wf {env envR : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (hcomp : decl.CompilesTo env block) (hrecsOf : decl.RecsOf block)
    (hWF : block.WF env) (hR : decl.addTypesCtorsProjsRecs env = some envR) :
    ∀ df ∈ block.rules, df.WF envR := by
  obtain ⟨envT, envC, envRec, hT, hC, hRec, -, -, -, hrules⟩ := hWF
  rw [← VInductDecl.recursorStage_eq hcomp hrecsOf hT hC hRec hR]
  exact hrules

/-- The compiled block behind a rule of a well-formed declaration: the compilation data at a
base environment, the installed containers, the block's well-formedness, and the generated
equation the rule is read off. -/
theorem VInductDecl.WF.rule_block {env : VEnv} {decl : VInductDecl} (hdecl : decl.WF env)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules) :
    ∃ (block : VInductBlock) (base : VEnv) (expanded : VInductDecl) (s : InductiveSignature)
      (g : InductiveSignature.Instance s) (aux : List InductiveSignature.ContainerSpecialization),
      CompiledInductive env decl block ∧ decl.RecsOf block ∧ block.WF env ∧ base ≤ env ∧
      InductiveSignature.CompilationData base decl expanded s g aux block ∧
      ContainersInstalled base aux ∧ ∃ df ∈ block.rules, VRecRule.OfEquation rec ru df := by
  obtain ⟨block, hcomp, hrecsOf, hWF⟩ := hdecl.recsCompiled
  obtain ⟨base, expanded, s, g, aux, hbase, C, hcont⟩ := hcomp.data
  exact ⟨block, base, expanded, s, g, aux, hcomp, hrecsOf, hWF, hbase, C, hcont,
    hrecsOf.rules rec hrec ru hru⟩

/-- The recursor of a generated recursor value of an ordinary block. -/
theorem InductiveSignature.CompilationData.ordinary_rec_of {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {decl : VInductDecl}
    (C : InductiveSignature.CompilationData base decl expanded s g [] block)
    (hrecsOf : decl.RecsOf block) (owner : Fin s.families.size) :
    ∃ r ∈ decl.recs, r.toVConstVal = g.recursor owner := by
  have hmem : g.recursor owner ∈ decl.recs.map (·.toVConstVal) := by
    rw [hrecsOf.recursors, C.ordinary_recursors]; exact g.recursor_mem owner
  obtain ⟨r, hr, e⟩ := List.mem_map.1 hmem
  exact ⟨r, hr, e⟩

/-- A rule of an ordinary block is read off a generated equation. -/
theorem InductiveSignature.CompilationData.ordinary_rule {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {rec : VRecursor} {ru : VRecRule} {df : VDefEq}
    (C : InductiveSignature.CompilationData base decl expanded s g [] block)
    (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df) :
    ∃ index : Fin s.constructors.size, df = g.equation index ∧
      rec.name = g.recursorName s.constructors[index].owner ∧
      rec.getMajorIdx = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].indices.length ∧
      ru.ctor = s.constructors[index].name ∧
      ru.ctorParams + ru.nfields = s.params.length + s.constructors[index].fields.length ∧
      ru.rhs = (g.equation index).rhs := by
  rw [C.ordinary_rules] at hdf
  obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf
  exact ⟨index, rfl, VRecRule.OfEquation.ordinary H⟩

/-! ## Constant support of the generated equations -/

namespace VExpr

@[simp] theorem containsAnyConst_bvar (names : List Name) (i : Nat) :
    (VExpr.bvar i).containsAnyConst names = false := rfl

@[simp] theorem containsAnyConst_sort (names : List Name) (u : VLevel) :
    (VExpr.sort u).containsAnyConst names = false := rfl

@[simp] theorem containsAnyConst_app (names : List Name) (f a : VExpr) :
    (VExpr.app f a).containsAnyConst names =
      (f.containsAnyConst names || a.containsAnyConst names) := rfl

@[simp] theorem containsAnyConst_lam (names : List Name) (A b : VExpr) :
    (VExpr.lam A b).containsAnyConst names =
      (A.containsAnyConst names || b.containsAnyConst names) := rfl

@[simp] theorem containsAnyConst_forallE (names : List Name) (A B : VExpr) :
    (VExpr.forallE A B).containsAnyConst names =
      (A.containsAnyConst names || B.containsAnyConst names) := rfl

@[simp] theorem containsAnyConst_const (names : List Name) (c : Name) (ls : List VLevel) :
    (VExpr.const c ls).containsAnyConst names = names.contains c := rfl

@[simp] theorem containsAnyConst_liftN (e : VExpr) (names : List Name) (n k : Nat) :
    (e.liftN n k).containsAnyConst names = e.containsAnyConst names := by
  induction e generalizing k <;> simp [VExpr.liftN, VExpr.containsAnyConst, *]

theorem containsAnyConst_mkApps (names : List Name) (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).containsAnyConst names =
      (fn.containsAnyConst names || args.any (·.containsAnyConst names)) := by
  induction args generalizing fn with
  | nil => simp
  | cons arg args ih =>
    rw [mkApps_cons, ih, containsAnyConst_app, List.any_cons, Bool.or_assoc]

theorem containsAnyConst_wrapLams (names : List Name) (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapLams ds b).containsAnyConst names =
      (ds.any (·.containsAnyConst names) || b.containsAnyConst names) := by
  induction ds with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons] at ih ⊢
    rw [containsAnyConst_lam, ih, List.any_cons, Bool.or_assoc]

theorem containsAnyConst_wrapForalls (names : List Name) (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapForalls ds b).containsAnyConst names =
      (ds.any (·.containsAnyConst names) || b.containsAnyConst names) := by
  induction ds with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at ih ⊢
    rw [containsAnyConst_forallE, ih, List.any_cons, Bool.or_assoc]

end VExpr

namespace InductiveSignature

theorem vars_containsAnyConst (names : List Name) (count below : Nat) :
    (vars count below).any (·.containsAnyConst names) = false := by
  show ((List.range count).reverse.map _).any _ = false
  rw [List.any_eq_false]
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact Bool.false_ne_true

/-- Mapping a constant-support-preserving function over an indexed list preserves the
support. -/
theorem any_map_zipIdx_congr (names : List Name) {f : VExpr → Nat → VExpr}
    (hf : ∀ e i, (f e i).containsAnyConst names = e.containsAnyConst names) :
    ∀ (ds : List VExpr) (k : Nat),
      ((ds.zipIdx k).map fun (t, i) => f t i).any (·.containsAnyConst names) =
        ds.any (·.containsAnyConst names)
  | [], _ => rfl
  | d :: ds, k => by
    simp only [List.zipIdx_cons, List.map_cons, List.any_cons, hf,
      any_map_zipIdx_congr names hf ds (k + 1)]

theorem insertBinders_any_containsAnyConst (names : List Name) (ds : List VExpr) (n : Nat) :
    (insertBinders ds n).any (·.containsAnyConst names) = ds.any (·.containsAnyConst names) := by
  unfold insertBinders
  exact any_map_zipIdx_congr names (f := fun t i => t.liftN n i)
    (fun _ _ => VExpr.containsAnyConst_liftN ..) ds 0

theorem any_zipIdx_fst {α : Type} (p : α → Bool) :
    ∀ (ds : List α) (k : Nat), (ds.zipIdx k).any (fun x => p x.1) = ds.any p
  | [], _ => rfl
  | d :: ds, k => by simp only [List.zipIdx_cons, List.any_cons, any_zipIdx_fst p ds (k + 1)]

theorem underFields_containsAnyConst (names : List Name) (e : VExpr) (a b c d k : Nat) :
    (Instance.underFields e a b c d k).containsAnyConst names = e.containsAnyConst names := by
  simp [Instance.underFields]

namespace Instance

variable {s : InductiveSignature} (g : Instance s)

/-- The constant support of a generated induction hypothesis: the recursive field's binders
and indices. -/
theorem hypothesis_containsAnyConst (names : List Name) (ctor : Constructor s.families.size)
    (priorMinors priorIHs field : Nat) (r : Recursive s.families.size) :
    (g.hypothesis ctor priorMinors priorIHs field r).containsAnyConst names =
      (r.binders.any (·.containsAnyConst names) || r.indices.any (·.containsAnyConst names)) := by
  simp only [Instance.hypothesis, VExpr.containsAnyConst_wrapForalls,
    VExpr.containsAnyConst_mkApps, List.any_append, List.any_map, VExpr.containsAnyConst_bvar,
    Function.comp_def, underFields_containsAnyConst, VExpr.containsAnyConst_instL,
    vars_containsAnyConst, List.any_cons, List.any_nil, Bool.or_false, Bool.false_or,
    any_zipIdx_fst]

/-- The constant support of a generated recursive call: the recursive field's binders and
indices and the recursor name of its target. -/
theorem recursiveCall_containsAnyConst (names : List Name) (ctor : Constructor s.families.size)
    (field : Nat) (r : Recursive s.families.size) :
    (g.recursiveCall ctor field r).containsAnyConst names =
      (r.binders.any (·.containsAnyConst names) || (names.contains (g.recursorName r.target) ||
        r.indices.any (·.containsAnyConst names))) := by
  simp only [Instance.recursiveCall, Instance.recursorHead, VExpr.containsAnyConst_wrapLams,
    VExpr.containsAnyConst_mkApps, List.any_append, List.any_map, VExpr.containsAnyConst_bvar,
    VExpr.containsAnyConst_const, Function.comp_def, underFields_containsAnyConst,
    VExpr.containsAnyConst_instL, vars_containsAnyConst, List.any_cons, List.any_nil,
    Bool.or_false, Bool.false_or, any_zipIdx_fst]

/-- A generated minor premise that avoids `names` has field types and recursive-field data
avoiding `names`. -/
theorem minor_containsAnyConst_inv (names : List Name) (ctor : Constructor s.families.size)
    (prior : Nat) (h : (g.minor ctor prior).containsAnyConst names = false) :
    (s.fieldTypes ctor).any (·.containsAnyConst names) = false ∧
    ∀ fr ∈ recursiveFields ctor,
      fr.2.binders.any (·.containsAnyConst names) = false ∧
      fr.2.indices.any (·.containsAnyConst names) = false := by
  simp only [Instance.minor, VExpr.containsAnyConst_wrapForalls, List.any_append,
    Bool.or_eq_false_iff, insertBinders_any_containsAnyConst, List.any_map,
    Function.comp_def, VExpr.containsAnyConst_instL] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  refine ⟨h1, fun fr hfr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfr
  have hmem : ((recursiveFields ctor)[i], i) ∈ (recursiveFields ctor).zipIdx := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simpa using hi, by simp⟩
  have := List.any_eq_false.1 h2 _ hmem
  simp only [hypothesis_containsAnyConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
  exact this

/-- The constant support of the reduct of a generated equation is bounded by the support of
the recursor type of any family (which lists every minor premise) and the recursor names. -/
theorem equation_rhs_containsAnyConst (names : List Name) (index : Fin s.constructors.size)
    (owner : Fin s.families.size)
    (hrec : (g.recursorType owner).containsAnyConst names = false)
    (hnames : ∀ o : Fin s.families.size, names.contains (g.recursorName o) = false) :
    (g.equation index).rhs.containsAnyConst names = false := by
  have hdoms : (g.params ++ g.motives ++ g.minors).any (·.containsAnyConst names) = false := by
    simp only [Instance.recursorType, VExpr.containsAnyConst_wrapForalls, List.any_append,
      Bool.or_eq_false_iff] at hrec
    simp only [List.any_append, Bool.or_eq_false_iff]
    exact hrec.1.1.1
  have hminor := List.any_eq_false.1 hdoms _ (List.mem_append_right _ (g.minor_mem index))
  obtain ⟨hfields, hrecf⟩ := g.minor_containsAnyConst_inv names s.constructors[index] index.val
    (Bool.eq_false_iff.2 hminor)
  rw [equation_rhs_eq, VExpr.containsAnyConst_wrapLams]
  simp only [eqDoms, eqBody, eqCalls, List.any_append, insertBinders_any_containsAnyConst,
    List.any_map, Function.comp_def, VExpr.containsAnyConst_instL,
    VExpr.containsAnyConst_mkApps, VExpr.containsAnyConst_bvar, vars_containsAnyConst,
    Bool.or_eq_false_iff, Bool.false_or]
  simp only [List.any_append, Bool.or_eq_false_iff] at hdoms
  refine ⟨⟨hdoms, hfields⟩, ?_⟩
  rw [List.any_eq_false]
  intro fr hfr
  obtain ⟨h1, h2⟩ := hrecf fr hfr
  simp only [recursiveCall_containsAnyConst, h1, h2, hnames, Bool.or_false, Bool.false_eq_true,
    not_false_eq_true]

end Instance

end InductiveSignature

end Lean4Lean
