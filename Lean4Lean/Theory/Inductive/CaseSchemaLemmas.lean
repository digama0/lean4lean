import Lean4Lean.Theory.Inductive.CaseSchema

/-! Pure shape facts about generated and restored abstract case equations. -/

namespace Lean4Lean
namespace VExpr

private theorem spine_head_go (e : VExpr) (args : List VExpr) :
    (getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app f a ih _ => exact (ih (a :: args)).trans (ih [a]).symm
  | _ => rfl

private theorem spine_head_app (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs.1 = fn.getAppFnArgs.1 := spine_head_go fn [arg]

private theorem spine_head_mkApps (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact (ih (.app fn a)).trans (spine_head_app fn a)

private theorem stripLams_of_head_elim {e : VExpr}
    (h : e.getAppFnArgs.1 = .elim block owner levels) : e.stripLams = e := by
  cases e <;> first | rfl | cases h

end VExpr
namespace InductiveSignature

theorem Restoration.equation_parts {r : Restoration} {source restored : VDefEq}
    (h : r.equation source = some restored) :
    r.expr source.lhs = some restored.lhs ∧ r.expr source.rhs = some restored.rhs ∧
      r.expr source.type = some restored.type := by
  simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, hl, rhs, hr, type, ht, h⟩ := h
  cases h
  exact ⟨hl, hr, ht⟩

/-- Successful restoration preserves the complete outer lambda constructor. -/
theorem Restoration.expr_lam_parts {r : Restoration} {domain body restored : VExpr}
    (h : r.expr (.lam domain body) = some restored) :
    ∃ domain' body', r.expr domain = some domain' ∧ r.expr body = some body' ∧
      restored = .lam domain' body' := by
  change (do
    let domain' ← r.expr domain
    let body' ← r.expr body
    pure (.lam domain' body')) = some restored at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨domain', hd, body', hb, h⟩ := h
  exact ⟨domain', body', hd, hb, Option.some.inj h.symm⟩

/-- Restoration cannot rename an abstract symbol or confuse it with a
constant, including when restoring the symbol's argument spine. -/
theorem Restoration.go_head_elim {r : Restoration} {e output : VExpr}
    {args : List VExpr} {block : Name} {owner : Nat} {levels : List VLevel}
    (hhead : e.getAppFnArgs.1 = .elim block owner levels)
    (hgo : Restoration.expr.go r e args = some output) :
    output.getAppFnArgs.1 = .elim block owner levels := by
  induction e generalizing args with
  | app fn arg ihfn _ =>
    have hf : fn.getAppFnArgs.1 = .elim block owner levels :=
      (VExpr.spine_head_app fn arg).symm.trans hhead
    cases ha : Restoration.expr.go r arg [] with
    | none => simp [Restoration.expr.go, ha] at hgo
    | some arg' =>
      simp [Restoration.expr.go, ha] at hgo
      exact ihfn hf hgo
  | elim b o ls =>
    have heq : b = block ∧ o = owner ∧ ls = levels := by simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using hhead
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [Restoration.expr.go, Option.some.injEq] at hgo
    subst output
    exact VExpr.spine_head_mkApps _ _
  | bvar | sort | const | lam | forallE | proj => cases hhead

theorem Restoration.wrapLams_head_elim {r : Restoration} {e output : VExpr}
    {domains : List VExpr} {block : Name} {owner : Nat} {levels : List VLevel}
    (hhead : e.getAppFnArgs.1 = .elim block owner levels)
    (h : r.expr (VExpr.wrapLams domains e) = some output) :
    output.stripLams.getAppFnArgs.1 = .elim block owner levels := by
  induction domains generalizing output with
  | nil =>
    have hh := Restoration.go_head_elim hhead h
    rw [VExpr.stripLams_of_head_elim hh]
    exact hh
  | cons d ds ih =>
    obtain ⟨d', b', _, hb, rfl⟩ := Restoration.expr_lam_parts h
    exact ih (output := b') hb

/-- Exact abstract head ownership survives restoration. -/
theorem Instance.restored_abstract_equation_head {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) {r : Restoration} {equation : VDefEq}
    (h : r.equation (g.equation index (.elim block firstOwner)) = some equation) :
    equation.lhs.stripLams.getAppFnArgs.1 =
      .elim block (firstOwner + s.constructors[index].owner.val) (g.targetLevel :: g.levels) := by
  have hl := (Restoration.equation_parts h).1
  apply Restoration.wrapLams_head_elim (h := hl)
  exact VExpr.spine_head_mkApps _ _

namespace CaseSchema

/-- Every case-view constructor is the `caseConstructor` of a constructor of the selected owner,
with the same ordered indices and field domains. -/
theorem view_constructor_eq_caseConstructor {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (index : Fin (schema.view owner).constructors.size) :
    ∃ ctor ∈ schema.signature.constructors.toList, ctor.owner = owner ∧
      (schema.view owner).constructors[index] = schema.caseConstructor ctor := by
  have hm : (schema.view owner).constructors[index] ∈ (schema.view owner).constructors.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem (xs := (schema.view owner).constructors) index.isLt)
  change (schema.view owner).constructors[index] ∈
    schema.signature.constructors.toList.filterMap (fun ctor =>
      if ctor.owner == owner then some (schema.caseConstructor ctor) else none) at hm
  obtain ⟨ctor, hctor, he⟩ := List.mem_filterMap.mp hm
  split at he
  · exact ⟨ctor, hctor, by simpa using ‹(ctor.owner == owner) = true›,
      (Option.some.inj he).symm⟩
  · cases he

/-- Each restored case rule comes from a specific constructor in the same
one-family view, with the exact abstract owner offset. -/
theorem equation_of_mem {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (h : schema.equations block owner U levels target = some rules) (hmem : rule ∈ rules) :
    ∃ index : Fin (schema.view owner).constructors.size,
      schema.restoration.equation
        ((schema.specialize owner U levels target).equation index (.elim block owner.val)) =
      some rule := by
  have hrel := List.mapM_eq_some.mp h
  have horigin : ∀ {xs ys}, List.Forall₂ (fun x y => schema.restoration.equation x = some y) xs ys →
      ∀ y ∈ ys, ∃ x ∈ xs, schema.restoration.equation x = some y := by
    intro xs ys hxy
    induction hxy with
    | nil => simp
    | cons hhead _ ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, .head _, hhead⟩
      · obtain ⟨x, hx, h⟩ := ih _ hy
        exact ⟨x, .tail _ hx, h⟩
  obtain ⟨generated, hgenerated, hrestore⟩ := horigin hrel _ hmem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hgenerated
  exact ⟨index, hrestore⟩

/-- Generic case rule heads use exactly the registered block and the owner
slot in the expanded signature, with target-first source-universe parameters. -/
theorem genericEquation_head {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (h : schema.genericEquations block owner = some rules) (hmem : rule ∈ rules) :
    rule.lhs.stripLams.getAppFnArgs.1 =
      .elim block owner.val (.param 0 :: schema.genericLevels) := by
  obtain ⟨index, hrestore⟩ := equation_of_mem h hmem
  have hhead := Instance.restored_abstract_equation_head _ index hrestore
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  simpa [specialize, hzero] using hhead

end CaseSchema
end InductiveSignature
end Lean4Lean

/-! ### Field types of the one-family view of a case schema

The constructors of the one-family view `schema.view owner` of a case schema have only external
fields, whose types are the constructor's field types in the schema's signature. -/

namespace Lean4Lean
namespace InductiveSignature

theorem fieldTypes_external (s : InductiveSignature) {c : Constructor s.families.size}
    {l : List VExpr} (h : c.fields = l.map Field.external) : s.fieldTypes c = l := by
  simp only [fieldTypes, h]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, fieldType]

namespace CaseSchema
variable {schema : CaseSchema} {owner : Fin schema.signature.families.size}

theorem view_fieldTypes_case (c : Constructor schema.signature.families.size) :
    (schema.view owner).fieldTypes (schema.caseConstructor c) = schema.signature.fieldTypes c :=
  fieldTypes_external _ rfl

theorem caseConstructor_recursiveFields (c : Constructor schema.signature.families.size) :
    Instance.recursiveFields (s := schema.view owner) (schema.caseConstructor c) = [] := by
  unfold Instance.recursiveFields
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hpair
  rcases pair with ⟨field, i⟩
  have hfield := List.fst_mem_of_mem_zipIdx hpair
  change field ∈ (schema.signature.fieldTypes c).map Field.external at hfield
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hfield
  rfl

end CaseSchema

end InductiveSignature
end Lean4Lean
