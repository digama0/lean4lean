import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive.CaseReductionLemmas

/-! The case certificate of a schema (`CaseSchema.Certified`) fixes the restoration parameter
boundary. Consequently every generated case rule of a registered schema recovers its binder
arguments, including for specialized auxiliary constructors, and all rules of one case family
have the same arity. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- A certified restoration specializes exactly the source common parameters,
which are the same parameters retained by the normalized signature. -/
theorem Certified.restoration_nparams {schema : CaseSchema}
    (H : schema.Certified base source block) :
    ∀ head ∈ schema.restoration.heads, head.nparams = schema.signature.params.length := by
  rcases H with ⟨expanded, auxiliaries, hdata, _, hr, _⟩
  intro head hhead
  rw [hr] at hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  have hn := hdata.model.nparams.trans hdata.nparams
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm

/-- Capturing a certified generated application after simultaneous
specialization recovers precisely the supplied equation arguments. -/
theorem Certified.capture_specialize {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (H : schema.Certified base source sourceBlock)
    (hgen : schema.Generates key owner rule)
    (hlen : arguments.length = rule.body.domains.length) :
    rule.capture (rule.application.specialize levels arguments) = arguments :=
  hgen.capture_specialize (fun head hhead => Nat.le_of_eq (H.restoration_nparams head hhead)) hlen

/-- Typed formation fixes the index count of every constructor selected for
this case family. The base environment must be well formed. -/
theorem Certified.view_constructor_indices {schema : CaseSchema}
    (H : schema.Certified base source block)
    (owner : Fin schema.signature.families.size)
    (index : Fin (schema.view owner).constructors.size) :
    (schema.view owner).constructors[index].indices.length =
      schema.signature.families[owner].indices.length := by
  rcases H with ⟨expanded, auxiliaries, hdata, _, _, _⟩
  obtain ⟨ctor, hctor, howner, hc⟩ := view_constructor_eq_caseConstructor index
  have harity := hdata.model.constructorArity ctor hctor
  rw [hc]
  simpa only [howner, caseConstructor] using harity

/-- All generated rules for a registered family take the same number of
arguments before the constructor major, including after nested restoration. -/
theorem Certified.arguments_length {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (H : schema.Certified base source block)
    (hgen : schema.Generates key owner rule) :
    rule.application.arguments.length = schema.signature.params.length + 1 +
      (schema.view owner).constructors.size + schema.signature.families[owner].indices.length :=
  hgen.arguments_length (fun head hhead => Nat.le_of_eq (H.restoration_nparams head hhead))
    (H.view_constructor_indices owner)

/-- Two rules of the same certified case family have identical applied arity. -/
theorem Certified.arguments_length_eq {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule rule' : AppliedRule}
    (H : schema.Certified base source block)
    (hgen : schema.Generates key owner rule) (hgen' : schema.Generates key owner rule') :
    rule.application.arguments.length = rule'.application.arguments.length :=
  (H.arguments_length hgen).trans (H.arguments_length hgen').symm

end Lean4Lean.InductiveSignature.CaseSchema
