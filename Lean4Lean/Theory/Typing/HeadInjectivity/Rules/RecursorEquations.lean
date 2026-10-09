import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Definitions

/-! # Syntax of ordinary recursor equations

For a finite compilation without container specializations (`auxiliaries = []`) the
restoration is the identity, the installed rules are the generated equations and the
installed recursors are the generated recursors. This file computes the pattern
decomposition of a generated equation (`Instance.equation_lhs_eq`), its coverage, the shape of
the recursor's type (`Instance.recursorType_eq_hi`), and the injectivity facts behind
uniqueness of the equations per head and constructor (`CompilationData.recursorName_inj`,
`CompilationData.ctor_inj`). -/

namespace Lean4Lean
namespace InductiveSignature

theorem compilationRestoration_nil (source : VInductDecl) :
    compilationRestoration source [] = {} := rfl

theorem CompilationData.ordinary_rules {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) : block.rules = g.equations := by
  have := H.equations
  rw [compilationRestoration_nil, Instance.restoredEquations_empty] at this
  exact (Option.some.inj this).symm

theorem CompilationData.ordinary_recursors {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) : block.recursors = g.recursors := by
  have := H.recursors
  rw [compilationRestoration_nil, Instance.restoredRecursors_empty] at this
  exact (Option.some.inj this).symm

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


theorem eqDoms_length : (g.eqDoms index).length =
    s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].fields.length := by
  simp only [eqDoms, Instance.params, Instance.motives, Instance.minors,
    insertBinders, fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
    Array.length_toList]
  omega

theorem eqLead_length : (g.eqLead index).length =
    s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length := by
  simp [eqLead, eqIndices]

theorem equation_lhs_eq : (g.equation index).lhs = .wrapLams (g.eqDoms index)
    (.mkApps (.const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars))
      (g.eqLead index ++ [.mkApps (.const s.constructors[index].name g.levels)
        (eqMs index ++ (eqFs index).map .bvar)])) := by
  simp only [equation, constructorApp, recursorHead, eqDoms, eqLead, eqMs, eqFs, eqIndices,
    InductiveSignature.vars_zero, List.append_assoc]

theorem equation_rhs_eq : ∃ body, (g.equation index).rhs = .wrapLams (g.eqDoms index) body :=
  ⟨_, rfl⟩

theorem equation_type_eq : (g.equation index).type = .wrapForalls (g.eqDoms index)
    (.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
      (s.families.size - 1 - s.constructors[index].owner.val)))
      (g.eqIndices index ++ [g.constructorApp s.constructors[index]
        (s.families.size + s.constructors.size) 0])) := rfl

theorem equation_uvars : (g.equation index).uvars = g.uvars := rfl

theorem equation_cov : ∀ x < (g.eqDoms index).length,
    VExpr.bvar x ∈ g.eqLead index ∨ x ∈ eqFs index := by
  intro x hx
  rw [eqDoms_length] at hx
  by_cases hxf : x < s.constructors[index].fields.length
  · exact .inr (by simpa [eqFs] using hxf)
  · exact .inl (List.mem_append_left _ (InductiveSignature.mem_vars (by omega) (by omega)))

/-- The binder domains of the generated recursor's type. -/
def recDoms (owner : Fin s.families.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size) ++
    [g.familyApp owner (vars s.params.length ((s.families.size + s.constructors.size) +
      s.families[owner].indices.length)) (vars s.families[owner].indices.length 0)]

theorem recursorType_eq_hi (owner : Fin s.families.size) :
    ∃ RH, (g.recursor owner).type = .wrapForalls (g.recDoms owner) RH :=
  ⟨VExpr.mkApps (.bvar ((insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)).length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val)))
    (vars (insertBinders (s.families[owner].indices.map (·.instL g.levels))
      (s.families.size + s.constructors.size)).length 1 ++ [.bvar 0]), by
    simp only [recursor, recursorType, recDoms, Instance.familyApp, insertBinders,
      List.length_map, List.length_zipIdx]⟩

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

end Instance

theorem filterMap_idx_inj {α β γ : Type} {f : α → Option β} {h : β → γ} :
    ∀ {l : List α}, ((l.filterMap f).map h).Nodup → ∀ {i j : Nat} (hi : i < l.length)
      (hj : j < l.length) {b b' : β}, f l[i] = some b → f l[j] = some b' → h b = h b' → i = j
  | [], _, _, _, hi, _, _, _, _, _, _ => nomatch hi
  | a :: t, hnd, i, j, hi, hj, b, b', hfi, hfj, e => by
    match i, j with
    | 0, 0 => rfl
    | 0, k + 1 =>
      exfalso
      simp only [List.getElem_cons_zero] at hfi
      simp only [List.getElem_cons_succ] at hfj
      simp only [List.filterMap_cons, hfi, List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (List.mem_map.2 ⟨b', List.mem_filterMap.2 ⟨_, List.getElem_mem _, hfj⟩, e.symm⟩)
    | k + 1, 0 =>
      exfalso
      simp only [List.getElem_cons_zero] at hfj
      simp only [List.getElem_cons_succ] at hfi
      simp only [List.filterMap_cons, hfj, List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (List.mem_map.2 ⟨b, List.mem_filterMap.2 ⟨_, List.getElem_mem _, hfi⟩, e⟩)
    | k + 1, k' + 1 =>
      simp only [List.getElem_cons_succ] at hfi hfj
      have hnd' : ((t.filterMap f).map h).Nodup := by
        cases hfa : f a with
        | none => simpa [List.filterMap_cons, hfa] using hnd
        | some c => simp only [List.filterMap_cons, hfa, List.map_cons, List.nodup_cons] at hnd
                    exact hnd.2
      have := filterMap_idx_inj hnd' (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
        hfi hfj e
      omega

theorem CompilationData.recursorName_inj {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g aux block) {o o' : Fin s.families.size}
    (h : g.recursorName o = g.recursorName o') : o = o' := by
  have hnd := H.generatedNames
  rw [List.map_append] at hnd
  have hnd := (List.nodup_append.1 hnd).2.1
  simp only [Instance.recursors, List.map_map] at hnd
  exact VEnv.inj_on_of_nodup_map hnd (List.mem_finRange _) (List.mem_finRange _) h

theorem CompilationData.ctor_inj {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g aux block) {i j : Fin s.constructors.size}
    (ho : s.constructors[i].owner = s.constructors[j].owner)
    (hn : s.constructors[i].name = s.constructors[j].name) : i = j := by
  obtain ⟨src, hsrc, -, -, -, -, hnames⟩ := H.model.family s.constructors[i].owner
  have hfam := (List.pairwise_flatMap.mp (familyNames_nodup H.expandedWF.2.1)).1 src hsrc
  have hnd := (List.nodup_cons.mp hfam).2
  rw [← hnames] at hnd
  simp only [declarationFamily, List.map_filterMap] at hnd
  apply Fin.ext
  refine filterMap_idx_inj (h := id) (b := s.constructors[i].name)
    (b' := s.constructors[j].name) (by simpa using hnd)
    (by exact i.isLt) (by exact j.isLt) ?_ ?_ hn
  · simp
  · have := congrArg Fin.val ho
    simp only [Fin.getElem_fin] at this
    simp [this]

/-- The installed constructor of an ordinary compilation returns its owner's family. -/
theorem CompilationData.ordinary_ctor {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) (index : Fin s.constructors.size) :
    ∃ fc ∈ source.constructorConstants, fc.name = s.constructors[index].name ∧
      ∃ ls, fc.type.forallResult.getAppFnArgs.1 =
        .const s.families[s.constructors[index].owner].name ls := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  rw [List.append_nil] at hfamily
  have hname : s.families[s.constructors[index].owner].name = family.name := hrel.name
  obtain ⟨fc, hfc, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  obtain ⟨_, _, _, _, _, hraw⟩ := H.sourceParameters
  obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw family hfamily fc hfc
  refine ⟨fc, List.mem_flatMap.mpr ⟨family, hfamily, hfc⟩, hrelctor.1.symm, ?_⟩
  rw [hname]
  have h2 := hhead
  rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
  exact ⟨_, h2⟩

theorem CompilationData.ordinary_expanded_types {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g [] block) :
    expanded.typeConstants = source.typeConstants := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  have h1 := Lean4Lean.List.Forall₂.length_eq hfamilies
  have h2 := Lean4Lean.List.Forall₂.length_eq H.model.families
  rw [H.headerPrefix, List.take_of_length_le]
  simp only [VInductDecl.typeConstants, List.length_map] at h1 h2 ⊢
  simp at h1
  omega

end InductiveSignature

theorem VInductBlock.install_recursor_lookup (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.recursors) :
    installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact VEnv.addDefEqRules_le.constants (VEnv.addConstVals_get hr hvalue)

end Lean4Lean
