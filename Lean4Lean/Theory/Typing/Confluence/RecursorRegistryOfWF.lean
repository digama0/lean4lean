import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.DefinitionPatterns

/-! The actual `WF'` derivation constructs its recursor table. Every inductive
installation contributes the descriptors of its retained compilation, including
compilations replayed from an earlier base. Equation coverage is proved along
that same construction; it is not an input registry assumption. -/
namespace Lean4Lean.VEnv
open InductiveSignature RecursorData
open private declaration_le definitionRegistry_decl_new definitionRegistry_decl_preserves
  from Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
set_option Elab.async false
set_option maxRecDepth 2048
variable {env extended : VEnv} {declarations : List VDecl}
  {table : Name → Option RecursorData} {equation : VDefEq}

/-- Exact syntactic coverage of an installed equation by the two generated
name tables or the fixed quotient rule. -/
def RecursorRegistryEquationCovered (declarations : List VDecl)
    (table : Name → Option RecursorData) (equation : VDefEq) : Prop :=
  (∃ value, definitionRegistry declarations value.name = some value ∧ equation = value.toDefEq) ∨
  (.quot ∈ declarations ∧ equation = quotDefEq) ∨
  ∃ data, table data.name = some data ∧
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.equation index = some equation

private theorem RecursorRegistryEquationCovered.declaration
    (history : env.WF' declarations) (declaration : VDecl.WF env d extended)
    (covered : RecursorRegistryEquationCovered declarations table equation) :
    RecursorRegistryEquationCovered (d :: declarations) table equation := by
  rcases covered with ⟨value, lookup, equal⟩ | ⟨member, equal⟩ | recursor
  · exact .inl ⟨value, definitionRegistry_decl_preserves declaration
      (history.definitionRegistry_registered lookup).1 lookup, equal⟩
  · exact .inr (.inl ⟨List.mem_cons_of_mem _ member, equal⟩)
  · exact .inr (.inr recursor)

private theorem RecursorRegistryEquationCovered.install
    {base installBase : VEnv} {source expanded : VInductDecl} {block : VInductBlock}
    (history : RecursorRegistryHistory installBase declarations table)
    (compilation : CompilationData base source expanded signature generated auxiliaries block)
    (installed : block.install installBase = some extended)
    (covered : RecursorRegistryEquationCovered declarations table equation) (key : Name) :
    RecursorRegistryEquationCovered (.induct source :: declarations)
      (installEntries table (compilationEntries key source signature auxiliaries generated)) equation := by
  rcases covered with definition | quotient | ⟨data, lookup, index, owner, equationEq⟩
  · exact .inl definition
  · exact .inr (.inl ⟨List.mem_cons_of_mem _ quotient.1, quotient.2⟩)
  · exact .inr (.inr ⟨data,
      compilation.recursorEntries_preserves installed (history.registered lookup).1 lookup,
      index, owner, equationEq⟩)

/-- Every well-formed declaration history produces an actual recursor registry
history and exact coverage of all its installed equations. The construction
uses the original compilation base retained by `CompiledInductive.replay`.
No abstract eliminator-schema registration is required. -/
theorem WF'.recursorRegistry (formed : env.WF' declarations) :
    ∃ table : Name → Option RecursorData,
      RecursorRegistryHistory env declarations table ∧
      ∀ equation, env.defeqs equation → RecursorRegistryEquationCovered declarations table equation := by
  induction formed with
  | empty => exact ⟨fun _ => none, .empty, fun _ absent => by cases absent⟩
  | decl declaration previous ih =>
    obtain ⟨table, history, covered⟩ := ih
    cases declaration with
    | «axiom» typed installed =>
      refine ⟨table, .decl history (.axiom typed installed), ?_⟩
      intro equation present
      exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
        previous (.axiom typed installed)
    | «opaque» typed installed =>
      refine ⟨table, .decl history (.opaque typed installed), ?_⟩
      intro equation present
      exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
        previous (.opaque typed installed)
    | «example» typed =>
      exact ⟨table, .decl history (.example typed), fun equation present =>
        (covered equation present).declaration previous (.example typed)⟩
    | «def» typed installed =>
      refine ⟨table, .decl history (.def typed installed), ?_⟩
      intro equation present
      rcases present with rfl | present
      · exact .inl ⟨_, definitionRegistry_decl_new (.def typed installed)
          (List.mem_singleton_self _), rfl⟩
      · exact (covered equation (by rwa [VEnv.addConst_defeqs installed] at present)).declaration
          previous (.def typed installed)
    | mutualDef headers installed bodies =>
      refine ⟨table, .decl history (.mutualDef headers installed bodies), ?_⟩
      intro equation present
      rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or] at present
      rcases present with member | present
      · obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
        exact .inl ⟨value, definitionRegistry_decl_new
          (.mutualDef headers installed bodies) valueMember, rfl⟩
      · exact (covered equation (by
          rwa [VEnv.addConstVals_defeqs (VEnv.addConsts_eq_addConstVals ▸ installed)] at present)).declaration
          previous (.mutualDef headers installed bodies)
    | quot ready installed =>
      refine ⟨table, .decl history (.quot ready installed), ?_⟩
      intro equation present
      have declaration := VDecl.WF.quot ready installed
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := installed
      rcases present with rfl | present
      · exact .inr (.inl ⟨List.mem_cons_self, rfl⟩)
      · exact (covered equation (by
          rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at present)).declaration previous declaration
    | induct installed =>
      rename_i source
      cases installed with
      | intro original compiled blockWF eliminatorsWF installed =>
        obtain ⟨base, expanded, signature, generated, auxiliaries, below, compilation, specializations⟩ :=
          compiled.exists_compilation
        let key : Name := (source.types.head?.map (·.name)).getD `recursorRegistry
        refine ⟨installEntries table (compilationEntries key _ signature auxiliaries generated),
          .induct history original compiled blockWF eliminatorsWF installed compilation
            specializations below, ?_⟩
        intro equation present
        have retain := RecursorRegistryEquationCovered.install history compilation installed
          (key := key) (equation := equation)
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at installed
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := installed
        rw [VEnv.addDefEqRules_defeqs_iff_mem_or] at present
        rcases present with member | present
        · obtain ⟨data, entry, index, owner, equationEq⟩ := compilation.recursorEntries_equation member key
          exact .inr (.inr ⟨data, compilation.recursorEntries_lookup entry, index, owner, equationEq⟩)
        · exact retain (covered equation (by
            rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at present))
  | inductEliminators baseHistory _ below registered constants equations projectionNames coherent
      fresh compat _ ih =>
    obtain ⟨table, history, covered⟩ := ih
    exact ⟨table, .eliminators history baseHistory below registered constants equations projectionNames
      coherent fresh compat,
      fun equation present => covered equation present⟩
  | inductProjections baseHistory _ hcovered sourceNames typeHeadersWF constructorUvars constructorsWF
      parameters shape types constructors projections addTypes addConstructors _ ih =>
    obtain ⟨table, history, covered⟩ := ih
    exact ⟨table, .projections history baseHistory hcovered sourceNames typeHeadersWF constructorUvars
      constructorsWF parameters shape types constructors projections addTypes addConstructors,
      fun equation present => covered equation
        (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using present)⟩

end Lean4Lean.VEnv
