import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.SignatureData

/-! # Syntactic shapes of the generated recursors and equations

The clauses `rec_shape` and `rule_shape` of `VInductDecl.WF` are syntactic. For a generated
recursor (`Instance.recursorType`) and a generated equation (`Instance.equation`) they follow
from the generator's definitions alone: the recursor telescope is `params ++ motives ++ minors
++ indices ++ [major]` ending in the owner's motive applied to the indices and the major, and
the reduct is the λ-closure of that telescope's first three groups and the fields around the
minor applied to the fields and the recursive calls. -/

namespace Lean4Lean
namespace InductiveSignature

open VExpr

private theorem piBinders_wrapForalls (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapForalls ds b).piBinders = ds ++ b.piBinders := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [VExpr.wrapForalls, VExpr.piBinders] at ih ⊢; exact ih

private theorem piArity_wrapForalls (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapForalls ds b).piArity = ds.length + b.piArity := by
  rw [← piBinders_length, piBinders_wrapForalls]; simp

private theorem piBody_wrapForalls (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapForalls ds b).piBody = b.piBody := by
  induction ds with
  | nil => rfl
  | cons d ds ih => exact ih

private theorem lamArity_wrapLams (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapLams ds b).lamArity = ds.length + b.lamArity := by
  induction ds with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons] at ih ⊢
    simp only [VExpr.lamArity, ih, List.length_cons]; omega

private theorem lamBody_wrapLams (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapLams ds b).lamBody = b.lamBody := by
  induction ds with
  | nil => rfl
  | cons d ds ih => exact ih

/-- An application spine headed by a bound variable or a constant is neither a Π nor a λ. -/
private theorem spine_notBinder {e : VExpr}
    (h : (∃ k, e.getAppFn = .bvar k) ∨ ∃ c us, e.getAppFn = .const c us) :
    e.piBinders = [] ∧ e.piBody = e ∧ e.lamArity = 0 ∧ e.lamBody = e := by
  cases e <;> simp_all [VExpr.getAppFn, VExpr.piBinders, VExpr.piBody, VExpr.lamArity,
    VExpr.lamBody]

private theorem getAppFn_mkApps_bvar (k : Nat) (args : List VExpr) :
    ((VExpr.bvar k).mkApps args).getAppFn = .bvar k := by simp [VExpr.getAppFn]

private theorem getAppFn_mkApps_const (c : Name) (us : List VLevel) (args : List VExpr) :
    ((VExpr.const c us).mkApps args).getAppFn = .const c us := by simp [VExpr.getAppFn]

private theorem vars_eq_bvarsDesc (count below : Nat) : vars count below = bvarsDesc below count := rfl

private theorem vars_length' (count below : Nat) : (vars count below).length = count := by
  simp [vars]

private theorem bvarsDesc_succ_zero (n : Nat) :
    bvarsDesc 0 (n + 1) = bvarsDesc 1 n ++ [.bvar 0] := by
  simp only [bvarsDesc, List.range_succ_eq_map, List.reverse_cons, List.map_append,
    List.map_reverse, List.map_map, List.map_cons, List.map_nil]
  simp [Function.comp_def, Nat.add_comm]

private theorem app_off {l₁ l₂ : List VExpr} {n : Nat} (i : Nat) (h : n = l₁.length) :
    (l₁ ++ l₂)[n + i]? = l₂[i]? := by
  subst h; rw [List.getElem?_append_right (by omega)]; simp

private theorem insertBinders_length' (F : List VExpr) (e : Nat) :
    (insertBinders F e).length = F.length := by simp [insertBinders]

@[simp] private theorem Instance.params_length {s : InductiveSignature} (g : Instance s) :
    g.params.length = s.params.length := by simp [Instance.params]

@[simp] private theorem Instance.motives_length {s : InductiveSignature} (g : Instance s) :
    g.motives.length = s.families.size := by simp [Instance.motives]

@[simp] private theorem Instance.minors_length {s : InductiveSignature} (g : Instance s) :
    g.minors.length = s.constructors.size := by simp [Instance.minors]

private theorem Instance.motives_getElem {s : InductiveSignature} (g : Instance s) (i : Nat)
    (hi : i < g.motives.length) :
    g.motives[i] = g.motive (s.families[i]'(by simpa using hi)) i := by
  simp [Instance.motives]

private theorem Instance.minors_getElem {s : InductiveSignature} (g : Instance s) (i : Nat)
    (hi : i < g.minors.length) :
    g.minors[i] = g.minor (s.constructors[i]'(by simpa using hi)) i := by
  simp [Instance.minors]

/-- The motive of a family has the motive shape: a telescope ending in a sort whose last binder
is headed by the family. -/
theorem Instance.motive_motiveFormer {s : InductiveSignature} (g : Instance s)
    (family : Family) (prior : Nat) :
    (g.motive family prior).motiveFormer? = some family.name := by
  simp only [Instance.motive, VExpr.motiveFormer?, piBinders_wrapForalls]
  simp [VExpr.piBinders, VExpr.headConst?, getAppFn_mkApps_const, VExpr.getAppFn]

theorem Instance.motive_motiveShape {s : InductiveSignature} (g : Instance s)
    (family : Family) (prior : Nat) : (g.motive family prior).MotiveShape := by
  refine ⟨⟨g.targetLevel, ?_⟩, by rw [g.motive_motiveFormer]; rfl⟩
  simp [Instance.motive, piBody_wrapForalls, VExpr.piBody]

/-- The minor premise of a constructor: its Π-telescope (fields and induction hypotheses), and
its Π-body, the owner's motive applied to the indices and the constructor application. -/
theorem Instance.minor_pi {s : InductiveSignature} (g : Instance s)
    (ctor : Constructor s.families.size) (prior : Nat) :
    (g.minor ctor prior).piArity = ctor.fields.length + (recursiveFields ctor).length ∧
    ∃ args, (g.minor ctor prior).piBody =
      (VExpr.bvar (ctor.fields.length + (recursiveFields ctor).length + prior +
        (s.families.size - 1 - ctor.owner.val))).mkApps
        (args ++ [g.constructorApp ctor (s.families.size + prior)
          (recursiveFields ctor).length]) := by
  let args := ctor.indices.map (fun e => ((e.instL g.levels).liftN
      (recursiveFields ctor).length).liftN (s.families.size + prior)
      (ctor.fields.length + (recursiveFields ctor).length))
  have hb := spine_notBinder (Or.inl ⟨_, getAppFn_mkApps_bvar
    (ctor.fields.length + (recursiveFields ctor).length + prior +
      (s.families.size - 1 - ctor.owner.val))
    (args ++ [g.constructorApp ctor (s.families.size + prior) (recursiveFields ctor).length])⟩)
  refine ⟨?_, args, ?_⟩
  · simp only [Instance.minor, List.length_map, List.length_zipIdx]
    rw [piArity_wrapForalls, ← piBinders_length, hb.1]
    simp [insertBinders_length', fieldTypes]
  · simp only [Instance.minor, List.length_map, List.length_zipIdx]
    rw [piBody_wrapForalls]
    exact hb.2.1

theorem Instance.minor_minorHeaded {s : InductiveSignature} (g : Instance s)
    (ctor : Constructor s.families.size) (prior : Nat) :
    (g.minor ctor prior).MinorHeaded prior s.families.size := by
  obtain ⟨harity, args, hbody⟩ := g.minor_pi ctor prior
  refine ⟨s.families.size - 1 - ctor.owner.val, by have := ctor.owner.isLt; omega, ?_⟩
  rw [hbody, getAppFn_mkApps_bvar, harity]; try (congr 1; omega)

theorem Instance.minor_minorFor {s : InductiveSignature} (g : Instance s)
    (ctor : Constructor s.families.size) (prior : Nat) :
    (g.minor ctor prior).MinorFor ctor.name := by
  obtain ⟨_, args, hbody⟩ := g.minor_pi ctor prior
  refine ⟨⟨_, by rw [hbody, getAppFn_mkApps_bvar]⟩,
    g.constructorApp ctor (s.families.size + prior) (recursiveFields ctor).length, ?_, ?_⟩
  · rw [hbody, VExpr.getAppArgs_mkApps]; simp [VExpr.getAppArgs]
  · rw [VExpr.headConst?_eq_some]
    exact ⟨g.levels, by simp [Instance.constructorApp, getAppFn_mkApps_const,
      VExpr.getAppFn]⟩

/-- `rec_shape` of a generated recursor. -/
theorem Instance.recursorType_recShape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) :
    (g.recursorType owner).RecShape s.params.length s.families.size s.constructors.size
      s.families[owner].indices.length := by
  have hfam : 0 < s.families.size := Nat.lt_of_le_of_lt (Nat.zero_le _) owner.isLt
  let extra := s.families.size + s.constructors.size
  let indices := insertBinders (s.families[owner].indices.map (·.instL g.levels)) extra
  have hind : indices.length = s.families[owner].indices.length := by
    simp [indices, insertBinders_length']
  let major := g.familyApp owner
    (vars s.params.length (extra + indices.length)) (vars indices.length 0)
  let result := VExpr.mkApps
      (.bvar (indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars indices.length 1 ++ [.bvar 0])
  have hty : g.recursorType owner =
      VExpr.wrapForalls (g.params ++ g.motives ++ g.minors ++ indices ++ [major]) result := rfl
  have hres := spine_notBinder (e := result) (Or.inl ⟨_, getAppFn_mkApps_bvar _ _⟩)
  have hbinders : (g.recursorType owner).piBinders =
      g.params ++ (g.motives ++ (g.minors ++ (indices ++ [major]))) := by
    rw [hty, piBinders_wrapForalls, hres.1, List.append_nil]; simp
  -- positions in the telescope
  have hmot : ∀ i (hi : i < s.families.size),
      (g.recursorType owner).piBinders[s.params.length + i]? =
        some (g.motive s.families[i] i) := by
    intro i hi
    rw [hbinders, app_off i (by simp), List.getElem?_append_left (by simp [hi]),
      List.getElem?_eq_getElem (by simpa using hi), g.motives_getElem]
  refine ⟨?_, ?_, ?_, owner.val, owner.isLt, ?_, ?_⟩
  · rw [← piBinders_length, hbinders]; simp [hind]; omega
  · intro i hi
    exact ⟨_, hmot i hi, g.motive_motiveShape _ _⟩
  · intro i hi
    refine ⟨g.minor s.constructors[i] i, ?_, g.minor_minorHeaded _ _⟩
    rw [hbinders, Nat.add_assoc, app_off _ (by simp), app_off i (by simp),
      List.getElem?_append_left (by simpa using hi),
      List.getElem?_eq_getElem (by simpa using hi), g.minors_getElem]
  · refine ⟨major, ?_, s.families[owner].name, ?_, ?_, _, hmot owner owner.isLt,
      g.motive_motiveFormer _ _⟩
    · rw [hbinders, Nat.add_assoc, Nat.add_assoc, app_off _ (by simp), app_off _ (by simp),
        app_off _ (by simp), ← hind, show indices.length = indices.length + 0 from rfl,
        app_off 0 rfl]
      rfl
    · rw [VExpr.headConst?_eq_some]
      exact ⟨g.levels, by simp [major, Instance.familyApp, InductiveSignature.familyApp,
        getAppFn_mkApps_const, VExpr.getAppFn]⟩
    · -- WAVE 3 COMPAT (restB): `MajorApp` is weakened; the generated major is its old shape.
      refine VExpr.MajorApp.of_params ⟨g.levels, ?_⟩
      simp only [major, Instance.familyApp, InductiveSignature.familyApp, vars_eq_bvarsDesc,
        hind]
      rfl
  · rw [hty, piBody_wrapForalls, hres.2.1]
    simp only [result, hind]
    rw [bvarsDesc_succ_zero, vars_eq_bvarsDesc]
    congr 2; omega

/-- `rule_shape` of a generated equation: the reduct of the equation of constructor `index`
is a `RuleShape` reduct for minor `index` of its owner's recursor, the minor binder being
`MinorFor` the constructor, with one recursive argument per binder of the minor after the
fields. -/
theorem Instance.equation_ruleShape {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) :
    ∃ A, (g.recursorType s.constructors[index].owner).piBinders[
        s.params.length + s.families.size + index.val]? = some A ∧
      A.MinorFor s.constructors[index].name ∧
      s.constructors[index].fields.length ≤ A.piArity ∧
      (g.equation index).rhs.RuleShape s.params.length s.families.size s.constructors.size
        s.constructors[index].fields.length
        (A.piArity - s.constructors[index].fields.length) index.val := by
  obtain ⟨harity, -⟩ := g.minor_pi s.constructors[index] index.val
  have hrt := g.recursorType_recShape s.constructors[index].owner
  refine ⟨g.minor s.constructors[index] index.val, ?_, g.minor_minorFor _ _,
    by rw [harity]; omega, ?_⟩
  · simp only [Instance.recursorType]
    rw [piBinders_wrapForalls,
      (spine_notBinder (Or.inl ⟨_, getAppFn_mkApps_bvar _ _⟩)).1, List.append_nil]
    simp only [List.append_assoc]
    rw [show s.params.length + s.families.size + index.val =
        s.params.length + (s.families.size + index.val) by omega,
      app_off (s.families.size + index.val) (by simp), app_off index.val (by simp),
      List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp),
      g.minors_getElem]
    rfl
  · rw [harity, Nat.add_sub_cancel_left]
    have hbody := spine_notBinder (e := VExpr.mkApps
      (.bvar (s.constructors[index].fields.length + s.constructors.size - 1 - index.val))
      (vars s.constructors[index].fields.length 0 ++
        (recursiveFields s.constructors[index]).map fun (field, r) =>
          g.recursiveCall s.constructors[index] field r .recursor))
      (Or.inl ⟨_, getAppFn_mkApps_bvar _ _⟩)
    refine ⟨?_, (recursiveFields s.constructors[index]).map fun (field, r) =>
      g.recursiveCall s.constructors[index] field r .recursor, by simp, ?_⟩
    · simp only [Instance.equation]
      rw [lamArity_wrapLams, hbody.2.2.1]
      simp [insertBinders_length', fieldTypes]; omega
    · simp only [Instance.equation]
      rw [lamBody_wrapLams, hbody.2.2.2, vars_eq_bvarsDesc]
      congr 2; omega

end InductiveSignature
end Lean4Lean
