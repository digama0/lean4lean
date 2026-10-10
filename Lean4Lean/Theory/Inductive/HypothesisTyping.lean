import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Typing of generated induction hypotheses, read off a well-formed recursor
type by peeling its binder telescope. -/

namespace Lean4Lean

/-- The `i`-th domain of a telescope, in a well-formed context extended by the
whole telescope, sits on top of a well-formed context made of the earlier
domains. -/
theorem OnCtx.getElem_reverse_append {P : List VExpr → VExpr → Prop}
    {L Γ : List VExpr} (h : OnCtx (L.reverse ++ Γ) P) (i : Nat) (hi : i < L.length) :
    OnCtx (L[i] :: ((L.take i).reverse ++ Γ)) P := by
  have e : L.reverse ++ Γ =
      (L.drop (i + 1)).reverse ++ (L[i] :: ((L.take i).reverse ++ Γ)) := by
    conv => lhs; rw [← List.take_append_drop i L, List.drop_eq_getElem_cons hi]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [e] at h
  exact OnCtx.of_append h

namespace InductiveSignature
namespace Instance

variable {s : InductiveSignature}

private theorem onCtx_reverse_split {P : List VExpr → VExpr → Prop}
    {A B C D E : List VExpr} (h : OnCtx ((A ++ B ++ C ++ D ++ E).reverse ++ []) P) :
    OnCtx (C.reverse ++ (B.reverse ++ A.reverse)) P := by
  simp only [List.reverse_append, List.append_nil, List.append_assoc] at h
  exact OnCtx.of_append (OnCtx.of_append h)

theorem length_minors (g : Instance s) : g.minors.length = s.constructors.size := by
  simp [minors]

theorem getElem_minors (g : Instance s) (i : Nat) (hi : i < g.minors.length) :
    g.minors[i] = g.minor (s.constructors[i]'(by simpa [length_minors] using hi)) i := by
  simp only [minors, List.getElem_map, List.getElem_zipIdx, Array.getElem_toList,
    Nat.zero_add]

/-- The minor premise of a constructor, and the context it is formed in, are
well-formed whenever some generated recursor type is well-formed. -/
theorem minor_onCtx_of_recursorType (g : Instance s)
    {env : VEnv} (henv : env.WF) (owner : Fin s.families.size)
    (H : env.IsType g.uvars [] (g.recursorType owner))
    (index : Fin s.constructors.size) :
    OnCtx (g.minor s.constructors[index] index.val ::
      ((g.minors.take index.val).reverse ++ (g.motives.reverse ++ g.params.reverse)))
      (env.IsType g.uvars) := by
  dsimp only [recursorType] at H
  have h1 := onCtx_reverse_split (VEnv.IsType.wrapForalls_inv henv (Γ := []) trivial H).1
  have hi : index.val < g.minors.length := by rw [length_minors]; exact index.isLt
  have h2 := OnCtx.getElem_reverse_append h1 index.val hi
  rw [getElem_minors] at h2
  exact h2

/-- The induction hypothesis together with its context is a well-formed context
whenever some generated recursor type is well-formed. -/
theorem hypothesis_onCtx_of_recursorType {s : InductiveSignature} (g : Instance s)
    {env : VEnv} (henv : env.WF) (owner : Fin s.families.size)
    (H : env.IsType g.uvars [] (g.recursorType owner))
    (index : Fin s.constructors.size) (j : Nat)
    (hj : j < (recursiveFields s.constructors[index]).length) :
    OnCtx (g.hypothesis s.constructors[index] index.val j
        (recursiveFields s.constructors[index])[j].1
        (recursiveFields s.constructors[index])[j].2 ::
      g.hypothesisContext s.constructors[index] index.val j) (env.IsType g.uvars) := by
  have hM := minor_onCtx_of_recursorType g henv owner H index
  have hm := hM.2
  dsimp only [minor] at hm
  have h1 := (VEnv.IsType.wrapForalls_inv henv hM.1 hm).1
  rw [List.reverse_append, List.append_assoc] at h1
  have hj' : j < ((recursiveFields s.constructors[index]).zipIdx.map fun ((field, r), i) =>
      g.hypothesis s.constructors[index] index.val i field r).length := by
    simpa using hj
  have h2 := OnCtx.getElem_reverse_append h1 j hj'
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at h2
  simpa only [hypothesisContext, List.append_assoc] using h2

/-- Every generated induction hypothesis is a well-formed type in its own
context whenever some generated recursor type is well-formed in the empty
context.  This is pure binder peeling of the recursor telescope: the minor
premise of the constructor sits in the context of the parameters, motives and
earlier minors, and the hypothesis sits under the fields and earlier
hypotheses of that minor. -/
theorem hypothesis_isType_of_recursorType {s : InductiveSignature} (g : Instance s)
    {env : VEnv} (henv : env.WF) (owner : Fin s.families.size)
    (H : env.IsType g.uvars [] (g.recursorType owner))
    (index : Fin s.constructors.size) (j : Nat)
    (hj : j < (recursiveFields s.constructors[index]).length) :
    env.IsType g.uvars (g.hypothesisContext s.constructors[index] index.val j)
      (g.hypothesis s.constructors[index] index.val j
        (recursiveFields s.constructors[index])[j].1
        (recursiveFields s.constructors[index])[j].2) :=
  (hypothesis_onCtx_of_recursorType g henv owner H index j hj).2

/-- The recursive-field clause of the generative specification holds in any
environment in which some generated recursor type is well-formed. -/
theorem generatedIHsWellTyped_of_recursorType {s : InductiveSignature} (g : Instance s)
    {env : VEnv} (henv : env.WF) (owner : Fin s.families.size)
    (H : env.IsType g.uvars [] (g.recursorType owner)) : g.GeneratedIHsWellTyped env :=
  hypothesis_isType_of_recursorType g henv owner H

end Instance
end InductiveSignature
end Lean4Lean
