import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Inductive.InstanceSpecialize
import Lean4Lean.Theory.Inductive.HypothesisTyping

/-! # Typing of a singleton family's telescopes, read off its recursor

The syntactic field and index telescopes of a normalized signature are only related to
the declared headers up to definitional equality in larger contexts, so their typing in
their own contexts cannot be read off the family and constructor headers (context
strengthening). The generated recursor type is typed syntactically: its motive is formed
over the index telescope, and its minor premise over the field telescope and the
induction hypotheses, beneath the motive. With elimination into `Prop` the motive is
instantiated at the constant family of the proposition `∀ p : Prop, p → p`, every
induction hypothesis is then inhabited, and instantiating the minor premise's context at
these inhabitants yields the field telescope's own typing, together with the typing of
the constructor's result indices along the index telescope. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s)

/-- The induction hypotheses of the first minor premise. -/
def hypotheses (c : Constructor s.families.size) : List VExpr :=
  (recursiveFields c).zipIdx.map fun ((field, r), i) => g.hypothesis c 0 i field r

@[simp] theorem length_insertBinders (l : List VExpr) (n : Nat) :
    (insertBinders l n).length = l.length := by simp [insertBinders]

theorem insertBinders_zero (l : List VExpr) : insertBinders l 0 = l := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i h1 h2; simp [insertBinders, VExpr.liftN_zero]

theorem motive_shape (owner : Fin s.families.size) (htarget : g.targetLevel = .zero) :
    g.motive s.families[owner] 0 =
      VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) := by
  simp only [motive, insertBinders_zero, htarget, indicesAt, majorType, List.length_map, Nat.zero_add]

theorem minor_shape (hfam : s.families.size = 1) (c : Constructor s.families.size)
    (hown : c.owner.val = 0) :
    g.minor c 0 =
      VExpr.wrapForalls (insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c)
        (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [g.constructorApp c 1 (g.hypotheses c).length])) := by
  have hnf : (g.fieldsAt c).length = c.fields.length := by simp [fieldsAt, fieldTypes]
  simp only [minor, hfam, hown, Nat.add_zero, Nat.sub_self, fieldsAt, hypotheses, ctorIndicesAt,
    List.length_map, List.length_zipIdx, List.map_map, Function.comp_def]
  have : (s.fieldTypes c).length = c.fields.length := by simp [fieldTypes]
  rw [this]

theorem toList_of_size_one {α} (a : Array α) (h : a.size = 1) (i : Fin a.size) :
    a.toList = [a[i]] := by
  have hi : i.val = 0 := by have := i.isLt; omega
  match a, h with
  | ⟨[x]⟩, _ => simp [hi]

theorem recursorType_shape (hfam : s.families.size = 1) (hcs : s.constructors.size = 1)
    (owner : Fin s.families.size) (index : Fin s.constructors.size) :
    g.recursorType owner =
      VExpr.wrapForalls (g.params ++ [g.motive s.families[owner] 0] ++
          [g.minor s.constructors[index] 0] ++ insertBinders (g.indicesAt owner) 2 ++
          [g.familyApp owner (vars s.params.length (2 + (g.indicesAt owner).length))
            (vars (g.indicesAt owner).length 0)])
        (VExpr.mkApps (.bvar ((g.indicesAt owner).length + 2))
          (vars (g.indicesAt owner).length 1 ++ [.bvar 0])) := by
  have ho : owner.val = 0 := by have := owner.isLt; omega
  have hi : index.val = 0 := by have := index.isLt; omega
  have hm : g.motives = [g.motive s.families[owner] 0] := by
    simp [motives, toList_of_size_one s.families hfam owner, ho]
  have hn : g.minors = [g.minor s.constructors[index] 0] := by
    simp [minors, toList_of_size_one s.constructors hcs index, hi]
  simp only [recursorType, hm, hn, hfam, hcs, ho, indicesAt, List.length_map, Nat.sub_self,
    Nat.add_zero, length_insertBinders]

end InductiveSignature.Instance

namespace VEnv
open InductiveSignature
variable {env : VEnv} {U : Nat}

theorem getElem_insertBinders {l : List VExpr} {n i : Nat} (h : i < (insertBinders l n).length) :
    (insertBinders l n)[i] = (l[i]'(by simpa using h)).liftN n i := by
  simp [insertBinders]

theorem vars_eq_bvarRange (count below : Nat) :
    vars count below = bvarRange count (count + below) := by
  apply List.ext_getElem
  · simp [vars, bvarRange]
  · intro i hi hi'
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range]
    rw [bvarRange_getElem count (count + below) i (by simpa [vars] using hi)]
    simp only [List.length_range]
    have : i < count := by simpa [vars] using hi
    congr 1
    omega


end VEnv

end Lean4Lean

namespace Lean4Lean
open VExpr VEnv

namespace InductiveSignature

/-- The first index that is literally the given field: the selector rule of
`CaseSchema.StructureTelescope.fieldIndex`. -/
def fieldSlot (CI : List VExpr) (nF i : Nat) : Option Nat :=
  (CI.zipIdx.find? fun (index, _) =>
    match index with
    | .bvar j => j == nF - 1 - i
    | _ => false).map Prod.snd

theorem fieldSlot_none {CI : List VExpr} {nF i : Nat} (h : fieldSlot CI nF i = none) :
    VExpr.bvar (nF - 1 - i) ∉ CI := by
  intro hmem
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hmem
  have zipped := List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hk)
  simp only [fieldSlot, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h _ zipped
  simp [he] at this

theorem fieldSlot_instL (CI : List VExpr) (ls : List VLevel) (nF i : Nat) :
    fieldSlot (CI.map (·.instL ls)) nF i = fieldSlot CI nF i := by
  simp only [fieldSlot, List.zipIdx_map, List.find?_map, Option.map_map]
  have hp : ((fun x : VExpr × Nat => match x.fst with
        | .bvar j => j == nF - 1 - i
        | _ => false) ∘ Prod.map (fun x => VExpr.instL ls x) id) =
      (fun x : VExpr × Nat => match x.fst with
        | .bvar j => j == nF - 1 - i
        | _ => false) := by
    funext ⟨e, k⟩; cases e <;> simp [VExpr.instL]
  rw [hp]
  rfl

theorem fieldSlot_spec {CI : List VExpr} {nF i k : Nat} (h : fieldSlot CI nF i = some k) :
    ∃ hk : k < CI.length, CI[k] = .bvar (nF - 1 - i) := by
  simp only [fieldSlot, Option.map_eq_some_iff] at h
  obtain ⟨⟨e, k'⟩, hf, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hmem)
  refine ⟨hlt, ?_⟩
  rw [he]
  cases e <;> simp_all

namespace Instance
variable {s : InductiveSignature} (g : Instance s)

/-- The constructor applied to the parameter and field variables. -/
def ctorApp (c : Constructor s.families.size) : VExpr :=
  VExpr.mkApps (.const c.name g.levels)
    (bvarRange (s.params.length + (g.fieldsAt c).length) (s.params.length + (g.fieldsAt c).length))

theorem constructorApp_shape (c : Constructor s.families.size) :
    g.constructorApp c 1 (g.hypotheses c).length =
      ((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
        ((g.fieldsAt c).length + (g.hypotheses c).length) := by
  have hnf : (g.fieldsAt c).length = c.fields.length := by simp [fieldsAt, fieldTypes]
  simp only [constructorApp, ctorApp, VExpr.liftN_mkApps, hnf]
  have hv := vars_eq_bvarRange c.fields.length 0
  simp only [Nat.add_zero] at hv
  rw [SingletonLayout.bvarRange_split, ← vars_eq_bvarRange, ← hv]
  simp only [List.map_append, List.map_map, Function.comp_def]
  congr 1
  congr 1 <;>
  · simp only [vars, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    simp only [VExpr.liftN, liftVar]
    split <;> split <;> (congr 1; omega)

theorem major_lift (owner : Fin s.families.size) :
    g.familyApp owner (vars s.params.length (2 + (g.indicesAt owner).length))
        (vars (g.indicesAt owner).length 0) =
      (g.majorType owner).liftN 2 (g.indicesAt owner).length := by
  simp only [familyApp, InductiveSignature.familyApp, majorType, indicesAt, List.length_map,
    VExpr.liftN_mkApps, List.map_append]
  rw [InductiveSignature.vars_map_liftN_hi _ _ _ _ (Nat.le_refl _), InductiveSignature.vars_map_liftN_lo _ _ _ _ (by omega)]
  simp [VExpr.liftN, Nat.add_comm]

/-- The cast specification of a singleton family at the instance's universes. -/
def singletonCast (owner : Fin s.families.size) (c : Constructor s.families.size)
    (sorts : List VLevel) : SingletonLayout where
  fields := g.fieldsAt c
  indices := g.indicesAt owner
  slot := (List.range (g.fieldsAt c).length).map
    (fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length)
  sorts := sorts

/-- The elimination into `Prop` of a singleton family through its recursor `h` at motive
universe zero; the minor premise abstracts the unused induction hypotheses. -/
def singletonElim (owner : Fin s.families.size) (c : Constructor s.families.size)
    (h : VExpr) : PropElim where
  family := .const s.families[owner].name g.levels
  ctor := .const c.name g.levels
  ctorIndices := g.ctorIndicesAt c
  elimHead := h
  minorOf M b := VExpr.wrapLams
    (VExpr.instDomains (insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c) M 0)
    (b.liftN (g.hypotheses c).length)

end Instance
end InductiveSignature
end Lean4Lean
