import Lean4Lean.Theory.Inductive.ProjNamesAvoid
import Lean4Lean.Theory.Typing.TelescopeConversion
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.CanonicalEq
import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Typing.ProjNamesTyping

/-! # Projection names of a case schema from those of its signature

A case schema without restoration generates its case type and case equations from the pieces of
its signature: parameters, family indices, constructor field domains and constructor result
indices. If every piece projects only out of structures satisfying `ok`, so do the generated
type and equations (`CaseSchema.projNamesOK_of_pieces`). -/

namespace Lean4Lean
open InductiveSignature

namespace VExpr

theorem projNamesOK_iff_avoid {ok : Name → Prop} :
    ∀ {e : VExpr}, e.ProjNamesOK ok ↔ ∀ n, ¬ ok n → e.projNamesAvoid [n] = true
  | .bvar _ | .sort _ | .const .. | .elim .. => by
    simp [ProjNamesOK, projNamesAvoid]
  | .app f a | .lam f a | .forallE f a => by
    simp only [ProjNamesOK, projNamesAvoid, Bool.and_eq_true]
    rw [projNamesOK_iff_avoid (e := f), projNamesOK_iff_avoid (e := a)]
    exact ⟨fun ⟨h1, h2⟩ n hn => ⟨h1 n hn, h2 n hn⟩,
      fun h => ⟨fun n hn => (h n hn).1, fun n hn => (h n hn).2⟩⟩
  | .proj m _ e => by
    simp only [ProjNamesOK, projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    rw [projNamesOK_iff_avoid (e := e)]
    constructor
    · rintro ⟨hm, he⟩ n hn
      exact ⟨fun h => hn (h ▸ hm), he n hn⟩
    · intro h
      refine ⟨Classical.byContradiction fun hm => (h m hm).1 rfl, fun n hn => (h n hn).2⟩

theorem ProjNamesOK.wrapForalls_inv {ok : Name → Prop} :
    ∀ {ds : List VExpr} {b : VExpr}, (VExpr.wrapForalls ds b).ProjNamesOK ok →
      (∀ d ∈ ds, d.ProjNamesOK ok) ∧ b.ProjNamesOK ok
  | [], _, h => ⟨by simp, h⟩
  | d :: ds, b, h => by
    obtain ⟨hd, hrest⟩ := h
    obtain ⟨hds, hb⟩ := ProjNamesOK.wrapForalls_inv (ds := ds) hrest
    refine ⟨fun x hx => ?_, hb⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hd
    · exact hds x hx

theorem ProjNamesOK.mkApps_inv {ok : Name → Prop} :
    ∀ {f : VExpr} {args : List VExpr}, (VExpr.mkApps f args).ProjNamesOK ok →
      f.ProjNamesOK ok ∧ ∀ a ∈ args, a.ProjNamesOK ok
  | _, [], h => ⟨h, by simp⟩
  | f, a :: args, h => by
    obtain ⟨⟨hf, ha⟩, hargs⟩ := ProjNamesOK.mkApps_inv (f := .app f a) (args := args) h
    refine ⟨hf, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hargs x hx

end VExpr

namespace InductiveSignature.Instance

variable {s : InductiveSignature} (g : Instance s) {names : List Name}

theorem motive_projNamesAvoid (family : Family) (prior : Nat)
    (h : ∀ e ∈ family.indices, e.projNamesAvoid names = true) :
    (g.motive family prior).projNamesAvoid names = true := by
  unfold motive
  dsimp only
  rw [VExpr.projNamesAvoid_wrapForalls_iff]
  refine ⟨fun d hd => ?_, rfl⟩
  rcases List.mem_append.1 hd with hd | hd
  · refine insertBinders_projNamesAvoid_iff.2 ?_ d hd
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simpa using h e0 he0
  · rw [List.mem_singleton] at hd
    subst hd
    refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha <;> exact vars_projNamesAvoid _ _ a ha

theorem minor_projNamesAvoid (ctor : Constructor s.families.size) (prior : Nat)
    (hrec : recursiveFields ctor = [])
    (hfields : ∀ e ∈ s.fieldTypes ctor, e.projNamesAvoid names = true)
    (hindices : ∀ e ∈ ctor.indices, e.projNamesAvoid names = true) :
    (g.minor ctor prior).projNamesAvoid names = true := by
  unfold minor
  dsimp only
  rw [hrec]
  simp only [List.zipIdx_nil, List.map_nil, List.append_nil, List.length_nil]
  rw [VExpr.projNamesAvoid_wrapForalls_iff, VExpr.projNamesAvoid_mkApps_iff]
  refine ⟨?_, rfl, ?_⟩
  · refine insertBinders_projNamesAvoid_iff.2 ?_
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simpa using hfields e0 he0
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 ha
      simpa using hindices e0 he0
    · rw [List.mem_singleton] at ha
      subst ha
      exact g.constructorApp_projNamesAvoid _ _ _

theorem recursorType_projNamesAvoid (owner : Fin s.families.size)
    (hparams : ∀ e ∈ s.params, e.projNamesAvoid names = true)
    (hindices : ∀ f ∈ s.families.toList, ∀ e ∈ f.indices, e.projNamesAvoid names = true)
    (hctors : ∀ c ∈ s.constructors.toList, recursiveFields c = [] ∧
      (∀ e ∈ s.fieldTypes c, e.projNamesAvoid names = true) ∧
      ∀ e ∈ c.indices, e.projNamesAvoid names = true) :
    (g.recursorType owner).projNamesAvoid names = true := by
  unfold recursorType
  dsimp only
  rw [VExpr.projNamesAvoid_wrapForalls_iff]
  refine ⟨fun d hd => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with (((hd | hd) | hd) | hd) | rfl
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 hd
      simpa using hparams e0 he0
    · unfold motives at hd
      obtain ⟨⟨family, i⟩, hmem, rfl⟩ := List.mem_map.1 hd
      exact g.motive_projNamesAvoid family i
        (hindices family (List.fst_mem_of_mem_zipIdx hmem))
    · unfold minors at hd
      obtain ⟨⟨ctor, i⟩, hmem, rfl⟩ := List.mem_map.1 hd
      obtain ⟨hrec, hf, hi⟩ := hctors ctor (List.fst_mem_of_mem_zipIdx hmem)
      exact g.minor_projNamesAvoid ctor i hrec hf hi
    · refine insertBinders_projNamesAvoid_iff.2 ?_ d hd
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      simpa using hindices _ (Array.getElem_mem_toList _) e0 he0
    · unfold familyApp InductiveSignature.familyApp
      refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with ha | ha <;> exact vars_projNamesAvoid _ _ a ha
  · refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · exact vars_projNamesAvoid _ _ a ha
    · rw [List.mem_singleton] at ha; subst ha; rfl

end InductiveSignature.Instance

namespace InductiveSignature.CaseSchema

/-- A schema without restoration projects only out of structures satisfying `ok` when every
piece of its signature does. -/
theorem projNamesOK_of_pieces {schema : CaseSchema} (hr : schema.restoration = {})
    {ok : Name → Prop}
    (hparams : ∀ e ∈ schema.signature.params, e.ProjNamesOK ok)
    (hindices : ∀ f ∈ schema.signature.families.toList, ∀ e ∈ f.indices, e.ProjNamesOK ok)
    (hfields : ∀ c ∈ schema.signature.constructors.toList,
      ∀ e ∈ schema.signature.fieldTypes c, e.ProjNamesOK ok)
    (hcindices : ∀ c ∈ schema.signature.constructors.toList, ∀ e ∈ c.indices, e.ProjNamesOK ok)
    (key : Name) :
    (∀ owner type, schema.genericType owner = some type → type.ProjNamesOK ok) ∧
    (∀ owner rules, schema.genericEquations key owner = some rules → ∀ df ∈ rules,
      df.lhs.ProjNamesOK ok ∧ df.rhs.ProjNamesOK ok ∧ df.type.ProjNamesOK ok) := by
  have htype : ∀ owner n, ¬ ok n →
      ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).recursorType
        (schema.viewOwner owner)).projNamesAvoid [n] = true := by
    intro owner n hn
    apply Instance.recursorType_projNamesAvoid
    · intro e he
      exact VExpr.projNamesOK_iff_avoid.1 (hparams e he) n hn
    · intro f hf e he
      simp only [view, List.mem_singleton] at hf
      have : f = schema.signature.families[owner] := by simpa using hf
      subst this
      exact VExpr.projNamesOK_iff_avoid.1
        (hindices _ (Array.getElem_mem_toList _) e he) n hn
    · intro c hc
      change c ∈ (List.filterMap (fun ctor => if ctor.owner == owner then
          some (schema.caseConstructor ctor) else none) schema.signature.constructors.toList :
            List (Constructor 1)).toArray.toList at hc
      rw [List.toList_toArray] at hc
      obtain ⟨c0, hc0, hc⟩ := List.mem_filterMap.1 hc
      split at hc
      · cases hc
        refine ⟨CaseSchema.caseConstructor_recursiveFields c0, ?_, ?_⟩
        · intro e he
          rw [CaseSchema.view_fieldTypes_case] at he
          exact VExpr.projNamesOK_iff_avoid.1 (hfields c0 hc0 e he) n hn
        · intro e he
          exact VExpr.projNamesOK_iff_avoid.1 (hcindices c0 hc0 e he) n hn
      · cases hc
  refine ⟨fun owner type h => ?_, fun owner rules h df hdf => ?_⟩
  · simp only [genericType, CaseSchema.type, hr, Restoration.expr_empty, Option.some.injEq] at h
    subst h
    exact VExpr.projNamesOK_iff_avoid.2 (htype owner)
  · simp only [genericEquations, CaseSchema.equations, hr] at h
    have hrules : ∀ (l rules : List VDefEq), l.mapM ({} : Restoration).equation = some rules →
        rules = l := by
      intro l
      induction l with
      | nil => intro rules h; simpa using h.symm
      | cons a l ih =>
        intro rules h
        rw [List.mapM_cons, Restoration.equation_empty] at h
        cases hl : l.mapM ({} : Restoration).equation with
        | none => simp [hl] at h
        | some l' =>
          simp [hl] at h
          subst h
          rw [ih l' hl]
    rw [hrules _ _ h] at hdf
    unfold Instance.equations at hdf
    obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf
    refine ⟨VExpr.projNamesOK_iff_avoid.2 fun n hn => ?_,
      VExpr.projNamesOK_iff_avoid.2 fun n hn => ?_, VExpr.projNamesOK_iff_avoid.2 fun n hn => ?_⟩
    · exact (Instance.equation_projNamesAvoid_of_recursorType _ _ (htype owner n hn) index _).1
    · exact (Instance.equation_projNamesAvoid_of_recursorType _ _ (htype owner n hn) index _).2.1
    · exact (Instance.equation_projNamesAvoid_of_recursorType _ _ (htype owner n hn) index _).2.2

end InductiveSignature.CaseSchema
end Lean4Lean
