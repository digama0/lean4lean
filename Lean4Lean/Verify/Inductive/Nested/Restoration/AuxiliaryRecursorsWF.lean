import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations

/-! Well-formedness of the restored auxiliary recursors and their rules, along the executable
auxiliary-recursor restoration fold of a nested run (section 3.3 of
the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Well-formedness along the auxiliary recursor-restoration fold: each restored
auxiliary recursor is well formed in `recursorEnv` and each of its restored rules in
`ruleEnv`. The two abstract environments are distinct: recursors are typed in the
recursor-checking environment, rules in the recursor environment. -/
inductive RestoredAuxiliaryRecursorsWF
    (safety : DefinitionSafety) (trEnv recursorEnv ruleEnv : VEnv)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
        {Htrace : FoldSteps
          (RestoredRecursorStep result loweredEnv auxRec allIndNames)
          names sourceEnv targetEnv}
        {priorRecursors : List VConstVal} {priorRules : List VDefEq}
        {finalRecursors : List VConstVal} {finalRules : List VDefEq},
      AuxiliaryRecursorRuleBatches safety trEnv Htrace
        priorRecursors priorRules finalRecursors finalRules →
      List VConstVal → List VDefEq → List VConstVal → List VDefEq → Prop
  | nil (sourceEnv : Environment) (recursors : List VConstVal)
      (rules : List VDefEq) :
      RestoredAuxiliaryRecursorsWF safety trEnv recursorEnv
        ruleEnv (.nil sourceEnv recursors rules) recursors rules recursors rules
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hsemantic : AuxiliaryRecursorRuleBatch safety trEnv
        Hstep)
      (Hrest : AuxiliaryRecursorRuleBatches safety trEnv
        Htail (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules)
      (Hrecursor : Hsemantic.recursor.toVConstant.WF recursorEnv)
      (Hrules : ∀ rule ∈ Hsemantic.rules, rule.WF ruleEnv)
      (Hfinal : RestoredAuxiliaryRecursorsWF safety trEnv
        recursorEnv ruleEnv Hrest
          (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules) :
      RestoredAuxiliaryRecursorsWF safety trEnv recursorEnv
        ruleEnv (.cons Hstep Htail Hsemantic Hrest) priorRecursors priorRules
          finalRecursors finalRules

theorem RestoredAuxiliaryRecursorsWF.recursorsWF
    (H : RestoredAuxiliaryRecursorsWF safety trEnv
      recursorEnv ruleEnv Haux priorRecursors priorRules finalRecursors
        finalRules)
    (Hprior : ∀ recursor ∈ priorRecursors,
      recursor.toVConstant.WF recursorEnv) :
    ∀ recursor ∈ finalRecursors,
      recursor.toVConstant.WF recursorEnv :=
  match H with
  | .nil _ _ _ => Hprior
  | .cons _ _ Hsemantic _ Hrecursor _ Hfinal =>
    Hfinal.recursorsWF (by
      intro recursor hrecursor
      rcases List.mem_append.mp hrecursor with hprior | hnew
      · exact Hprior recursor hprior
      · have : recursor = Hsemantic.recursor := by simpa using hnew
        subst recursor
        exact Hrecursor)

theorem RestoredAuxiliaryRecursorsWF.rulesWF
    (H : RestoredAuxiliaryRecursorsWF safety trEnv
      recursorEnv ruleEnv Haux priorRecursors priorRules finalRecursors
        finalRules)
    (Hprior : ∀ rule ∈ priorRules, rule.WF ruleEnv) :
    ∀ rule ∈ finalRules, rule.WF ruleEnv :=
  match H with
  | .nil _ _ _ => Hprior
  | .cons _ _ Hsemantic _ _ Hrules Hfinal =>
    Hfinal.rulesWF (by
      intro rule hrule
      rcases List.mem_append.mp hrule with hprior | hnew
      · exact Hprior rule hprior
      · exact Hrules rule hnew)

end VerifyInductive
end Lean4Lean
