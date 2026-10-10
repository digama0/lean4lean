import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.AddInduct

/-! Finite compilation from certified parameter specializations (section 2.2 of
the design notes).

Every container of a nested declaration is a previously installed block with its own finite
compilation derivation (`ContainersInstalled`). The chosen family fixes both the restoration heads and the entire
ordered constructor list. The normalized expanded signature determines every
recursor and equation; restoration accepts no independent equation templates.

`VInductDecl.CompilesTo` abbreviates this derivation; the block layout and
name uniqueness read by installation are accessor theorems of it.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- Select a family of a prior container and specialize its parameters.
Constructor names and their order are derived from this family. -/
structure ContainerSpecialization where
  container : VInductDecl
  family : Fin container.types.length
  auxiliary : Name
  levels : List VLevel
  arguments : List VExpr

namespace ContainerSpecialization

def source (a : ContainerSpecialization) : VInductiveType := a.container.types[a.family]

def constructorName (a : ContainerSpecialization) (ctor : VConstVal) : Name :=
  ctor.name.replacePrefix a.source.name a.auxiliary

/-- Only names obtained from the certified container can be restoration
targets. In particular callers cannot choose a replacement constructor body. -/
def heads (a : ContainerSpecialization) (uvars nparams : Nat) : List HeadSpecialization :=
  { auxiliary := a.auxiliary, uvars, nparams, target := a.source.name,
    levels := a.levels, arguments := a.arguments } ::
  a.source.ctors.map fun ctor =>
    { auxiliary := a.constructorName ctor, uvars, nparams, target := ctor.name,
      levels := a.levels, arguments := a.arguments }

/-- The direct auxiliary before recursive occurrences in its fields are
expanded. Its types are specialized from the prior source, never supplied by
the caller. Partial parameter telescopes fail explicitly. -/
def specializedFamily (a : ContainerSpecialization) (uvars : Nat)
    (params : List VExpr) : Option VInductiveType := do
  let type ← specializeType (a.source.type.instL a.levels) a.arguments
  let ctors ← a.source.ctors.mapM fun ctor => do
    let type ← specializeType (ctor.type.instL a.levels) a.arguments
    return ({
      name := a.constructorName ctor
      uvars := uvars
      type := VExpr.wrapForalls params type } : VConstVal)
  return {
    name := a.auxiliary
    uvars := uvars
    type := VExpr.wrapForalls params type
    numIndices := a.source.numIndices
    resultLevel := a.source.resultLevel.inst a.levels
    ctors := ctors }

/-- Scope, safety, and typing of an actual container parameter application.
The context contains the current block's common parameters; the environment
contains its source headers, but no current recursors or equations. -/
def WellFormed (a : ContainerSpecialization) (envTypes : VEnv)
    (source : VInductDecl) (params : List VExpr) : Prop :=
  a.arguments.length = a.container.nparams ∧
  (∀ arg ∈ a.arguments, arg.ClosedN source.nparams) ∧
  a.levels.length = a.container.uvars ∧
  (∀ level ∈ a.levels, level.WF source.uvars) ∧
  (source.isUnsafe = true ∨ a.container.isUnsafe = false) ∧
  ∃ type, envTypes.HasType source.uvars params.reverse
    (VExpr.mkApps (.const a.source.name a.levels) a.arguments) type

end ContainerSpecialization

/-- Restoration is fixed by the ordered finite specialization list.
The ordinary case is exactly the empty list and the identity restoration. -/
def compilationRestoration (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization) : Restoration where
  heads := auxiliaries.flatMap fun a => a.heads source.uvars source.nparams
  recursors := auxiliaries.zipIdx.map fun (a, i) =>
    (a.auxiliary.str "rec", (((source.types.head?).map (fun t : VInductiveType => t.name)).getD (default : Name)).str "rec" |>.appendIndexAfter (i + 1))

/-- Restoration of a type is exact syntax followed by typed equality.
Typing takes place before any equation from this compilation is installed. -/
def RestoresType (r : Restoration) (env : VEnv) (uvars : Nat)
    (normalized source : VExpr) : Prop :=
  ∃ restored, r.expr normalized = some restored ∧
    env.IsDefEqU uvars [] restored source

/-- Ordered family and constructor correspondence. For an auxiliary, `source`
is the direct specialization generated from its certified container.

The family type correspondence is deliberately weaker than restoration of the
normalized header: the source header is only required to be definitionally
some telescope whose body is definitionally the recorded sort (in the
telescope's own scope).  The normalized signature's family telescope is not
tied definitionally to the source header (see `Models`); what the generated
recursor needs from it is `FamilyTypesWF`. -/
structure RestoresFamily (r : Restoration) (envTypes : VEnv) (uvars : Nat)
    (normalized source : VInductiveType) : Prop where
  name : normalized.name = source.name
  universes : normalized.uvars = source.uvars
  indices : normalized.numIndices = source.numIndices
  resultLevel : normalized.resultLevel ≈ source.resultLevel
  type : ∃ domains body level exprType, level ≈ normalized.resultLevel ∧
    envTypes.IsDefEq uvars [] source.type (VExpr.wrapForalls domains body) exprType ∧
    envTypes.IsDefEq uvars domains.reverse body (.sort level) (.sort (.succ level))
  constructors : List.Forall₂ (fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
    RestoresType r envTypes uvars normalized.type source.type)
    normalized.ctors source.ctors

/-- The ordinary source model supplies the empty-restoration correspondence;
the global constructor list is split using the recorded family boundaries.
The family header shapes come from the source parameter formation. -/
theorem Models.restores_empty {s : InductiveSignature} {env envTypes : VEnv}
    {decl : VInductDecl} (H : s.Models env decl)
    (hparams : decl.SourceParameterWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    List.Forall₂ (RestoresFamily {} envTypes decl.uvars) s.declaration.types decl.types := by
  rcases H.constructors with ⟨oldTypes, holdTypes, hctors⟩
  have heq : oldTypes = envTypes := Option.some.inj (holdTypes.symm.trans htypes)
  subst oldTypes
  have hle := VEnv.addConstVals_le htypes
  rcases hparams with ⟨params, _, _, hsub, _, _⟩
  have hfamilies := H.families
  simp only [VInductDecl.constructorConstants] at hctors
  generalize s.declaration.types = left at hfamilies hctors ⊢
  generalize decl.types = right at hfamilies hctors hsub ⊢
  induction hfamilies with
  | nil => exact .nil
  | @cons normalized source left right h htail ih =>
    simp only [List.flatMap_cons] at hctors
    have hlength : normalized.ctors.length = source.ctors.length := by
      have := congrArg List.length h.2.2.2.2
      simpa using this
    rcases (Lean4Lean.List.Forall₂.append_of_left hlength).mp hctors with ⟨hhead, hrest⟩
    refine .cons ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_⟩
      (ih hrest (fun t ht => hsub t (List.mem_cons_of_mem _ ht)))
    · obtain ⟨domains, body, exprType, _, htype, hbody⟩ :=
        (hsub source List.mem_cons_self).header
      exact ⟨domains, body, source.resultLevel, exprType, h.2.2.2.1.symm,
        htype.mono hle, hbody.mono hle⟩
    · exact Lean4Lean.List.Forall₂.imp (fun n t hc =>
        ⟨hc.1, hc.2.1, n.type, Restoration.expr_empty _, hc.2.2⟩) hhead

/-- The part of a finite compilation that fixes an abstract case schema: formation of the
source and expanded declarations, the normalized model, the restoration correspondence and the
installed source constants. It omits everything about the generated recursors (their
names, freshness, types, equations, elimination universe and the typing of their induction
hypotheses), which the case eliminator rules `elimDF`/`elimIota` do not read. It is therefore
available once the constructors are installed, before any generated recursor has been checked. -/
structure CaseCompilationData (env : VEnv) (source expanded : VInductDecl)
    (s : InductiveSignature) (auxiliaries : List ContainerSpecialization)
    (block : VInductBlock) : Prop where
  sourceWF : VInductDecl.SourceWF env source
  sourceParameters : VInductDecl.SourceParameterWF env source
  expandedWF : VInductDecl.SourceWF env expanded
  headerPrefix : source.typeConstants = expanded.typeConstants.take source.types.length
  expandedFormation : VInductDecl.OrdinaryFormationWF env expanded
  model : s.Models env expanded
  uvars : expanded.uvars = source.uvars
  nparams : expanded.nparams = source.nparams
  safety : expanded.isUnsafe = source.isUnsafe
  restorationScoped : (compilationRestoration source auxiliaries).Scoped
  correspondence : ∃ envTypes direct,
    env.addConstVals source.typeConstants = some envTypes ∧
    auxiliaries.mapM (fun a => a.specializedFamily source.uvars s.params) = some direct ∧
    (∀ a ∈ auxiliaries, a.WellFormed envTypes source s.params) ∧
    List.Forall₂
      (RestoresFamily (compilationRestoration source auxiliaries) envTypes source.uvars)
      s.declaration.types (source.types ++ direct)
  /-- Well-formed family applications of the normalized signature, in the expanded
  constructor environment with the expanded declaration's projection entries. -/
  familyTypesWF : ∃ envExpandedTypes envExpandedCtors,
    env.addConstVals expanded.typeConstants = some envExpandedTypes ∧
    envExpandedTypes.addConstVals expanded.constructorConstants = some envExpandedCtors ∧
    s.FamilyTypesWF (envExpandedCtors.addProjections expanded.projectionEntries) expanded.uvars
  types : block.types = source.typeConstants
  ctors : block.ctors = source.constructorConstants
  projections : block.projections = source.projectionEntries

/-- The recursor names reserved by the restoration of a compilation (one per auxiliary family)
are fresh in the base environment and are not names of the source or expanded declaration. -/
def RecursorNamesFresh (env : VEnv) (source expanded : VInductDecl)
    (auxiliaries : List ContainerSpecialization) : Prop :=
  ∀ n ∈ (compilationRestoration source auxiliaries).recursors.map Prod.fst,
    env.constants n = none ∧ n ∉ source.sourceNames ∧ n ∉ expanded.sourceNames

/-- A single expansion fixes formation and the generated recursors and rules.
Every auxiliary family is covered, including semantically unused auxiliaries
introduced by erased concrete occurrences. -/
structure CompilationData (env : VEnv) (source expanded : VInductDecl)
    (s : InductiveSignature) (g : Instance s)
    (auxiliaries : List ContainerSpecialization) (block : VInductBlock) : Prop
    extends CaseCompilationData env source expanded s auxiliaries block where
  admissible : ∃ envExpandedTypes,
    env.addConstVals expanded.typeConstants = some envExpandedTypes ∧
    g.Admissible envExpandedTypes
  generatedIHsWellTyped : ∃ envExpandedTypes envExpandedCtors,
    env.addConstVals expanded.typeConstants = some envExpandedTypes ∧
    envExpandedTypes.addConstVals expanded.constructorConstants = some envExpandedCtors ∧
    g.GeneratedIHsWellTyped (envExpandedCtors.addProjections expanded.projectionEntries) ∧
    s.FamilyTypesWF (envExpandedCtors.addProjections expanded.projectionEntries) expanded.uvars
  recursorNames : ∀ owner, g.recursorName owner = s.families[owner].name.str "rec"
  generatedNames : ((expanded.typeConstants ++ expanded.constructorConstants ++
    g.recursors).map (·.name)).Nodup
  recursorsFresh : ∀ recursor ∈ g.recursors, env.constants recursor.name = none
  recursors : g.restoredRecursors (compilationRestoration source auxiliaries) =
    some block.recursors
  equations : g.restoredEquations (compilationRestoration source auxiliaries) =
    some block.rules
  names : ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup


end InductiveSignature

mutual

/-- Shared finite ordinary/nested compilation. Empty specializations give
ordinary compilation. A nested container is certified recursively by this
same judgment, so no container is justified by an environment lookup alone. -/
inductive CompiledInductive : VEnv → VInductDecl → VInductBlock → Prop
  | intro {env source expanded s g auxiliaries block} :
      InductiveSignature.CompilationData env source expanded s g auxiliaries block →
      ContainersInstalled env auxiliaries →
      CompiledInductive env source block
  | replay {base env source block} :
      CompiledInductive base source block →
      base ≤ env →
      block.WF env →
      CompiledInductive env source block

/-- Each selected container is a compiled block installed below the source environment
`env`. Current headers, current recursors, and future blocks cannot justify a specialization.
The mutual induction with `CompiledInductive` makes the tree of containers finite.

WAVE 2 COMPAT: the container is installed by `VEnv.addInduct` (its recursors and rules read
off the compiled block, `VInductDecl.RecsOf`), not by `VInductBlock.install`; see
`VEnv.InstalledBelow` in `Theory/Inductive.lean`. -/
inductive ContainersInstalled : VEnv →
    List InductiveSignature.ContainerSpecialization → Prop
  | nil {env} : ContainersInstalled env []
  | cons {env a rest base block installed} :
      CompiledInductive base a.container block →
      block.WF base →
      a.container.RecsOf block →
      base.addInduct a.container = some installed →
      installed ≤ env →
      ContainersInstalled env rest →
      ContainersInstalled env (a :: rest)

end

/-- A compilation remains one over a larger environment in which its block is still well
formed (the `replay` constructor). Lowering-only names need
not remain fresh in the larger environment, since they are never installed
there; freshness and checking of the actual output are required explicitly. -/
theorem CompiledInductive.mono {base env source block}
    (H : CompiledInductive base source block) (hle : base ≤ env)
    (Hblock : block.WF env) : CompiledInductive env source block :=
  .replay H hle Hblock

/-- The block of a compilation lays out the source declaration's families. -/
theorem CompiledInductive.types_eq {env source block} (H : CompiledInductive env source block) :
    block.types = source.typeConstants := by
  induction H using CompiledInductive.rec (motive_2 := fun _ _ _ => True) with
  | intro h _ _ => exact h.types
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ => trivial

/-- The block of a compilation lays out the source declaration's constructors. -/
theorem CompiledInductive.ctors_eq {env source block} (H : CompiledInductive env source block) :
    block.ctors = source.constructorConstants := by
  induction H using CompiledInductive.rec (motive_2 := fun _ _ _ => True) with
  | intro h _ _ => exact h.ctors
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ => trivial

/-- The block of a compilation lays out the source declaration's projections. -/
theorem CompiledInductive.projections_eq {env source block}
    (H : CompiledInductive env source block) :
    block.projections = source.projectionEntries := by
  induction H using CompiledInductive.rec (motive_2 := fun _ _ _ => True) with
  | intro h _ _ => exact h.projections
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ => trivial

/-- The installed names of a compiled block are distinct. -/
theorem CompiledInductive.names_nodup {env source block}
    (H : CompiledInductive env source block) :
    ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup := by
  induction H using CompiledInductive.rec (motive_2 := fun _ _ _ => True) with
  | intro h _ _ => exact h.names
  | replay _ _ _ ih => exact ih
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ => trivial

/-- Ordinary compilation (`Compiles`) is the zero-specialization case of the
same finite derivation. Formation and output checking are supplied by their
existing independent judgments. -/
theorem CompiledInductive.ordinary {env : VEnv} {source : VInductDecl}
    {block : VInductBlock}
    (Hsource : VInductDecl.SourceWF env source)
    (Hformation : VInductDecl.OrdinaryFormationWF env source)
    (Hcanonical : InductiveSignature.Compiles env source block)
    (Hblock : block.WF env)
    (htypes : block.types = source.typeConstants)
    (hctors : block.ctors = source.constructorConstants)
    (hprojections : block.projections = source.projectionEntries)
    (hnames : ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup) :
    CompiledInductive env source block := by
  rcases Hcanonical.generated with ⟨s, g, envTypes, Hmodel, hadded, Hadmissible, Hrec,
    hrecNames, hrecs, hrules⟩
  have hrestore : InductiveSignature.compilationRestoration source [] = {} := rfl
  have hfresh : ∀ recursor ∈ block.recursors, env.constants recursor.name = none := by
    rcases Hblock with ⟨typesEnv, ctorsEnv, recsEnv, ht, hc, hr, _⟩
    have hle := (VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)
    intro recursor hrec
    have hf := VEnv.addConstVals_names_fresh hr recursor hrec
    cases he : env.constants recursor.name with
    | none => rfl
    | some value =>
      have hv := hle.constants he
      simp only [VEnv.addProjections_constants] at hf
      rw [hv] at hf
      contradiction
  apply CompiledInductive.intro (expanded := source) (s := s) (g := g)
    (auxiliaries := []) ?_ .nil
  refine {
    sourceWF := Hsource
    sourceParameters := Hformation.sourceParameterWF
    expandedWF := Hsource
    headerPrefix := (List.take_of_length_le (by simp [VInductDecl.typeConstants])).symm
    expandedFormation := Hformation
    model := Hmodel
    uvars := rfl
    nparams := rfl
    safety := rfl
    restorationScoped := ?_
    correspondence := ?_
    admissible := ⟨envTypes, hadded, Hadmissible⟩
    generatedIHsWellTyped := let ⟨envCtors, hc, hwf, hfam⟩ := Hrec
      ⟨envTypes, envCtors, hadded, hc, hwf, hfam⟩
    familyTypesWF := let ⟨envCtors, hc, _, hfam⟩ := Hrec
      ⟨envTypes, envCtors, hadded, hc, hfam⟩
    recursorNames := hrecNames
    generatedNames := ?_
    recursorsFresh := ?_
    types := htypes
    ctors := hctors
    projections := hprojections
    recursors := ?_
    equations := ?_
    names := hnames }
  · simp [hrestore, InductiveSignature.Restoration.Scoped]
  · refine ⟨envTypes, [], hadded, rfl, ?_, ?_⟩
    · simp
    · simpa only [hrestore, List.append_nil] using Hmodel.restores_empty Hformation.sourceParameterWF hadded
  · simpa only [← hrecs, ← htypes, ← hctors] using hnames
  · simpa only [← hrecs] using hfresh
  · simp [hrestore, hrecs]
  · simp [hrestore, hrules]

end Lean4Lean

namespace Lean4Lean.InductiveSignature

/-- The case part of an ordinary compilation (no auxiliaries), from the source and formation
judgments, a model of the declaration, and the family typing of the signature. -/
theorem CaseCompilationData.ofOrdinary {env : VEnv} {source : VInductDecl}
    {s : InductiveSignature} {block : VInductBlock} {envTypes envCtors : VEnv}
    (Hsource : VInductDecl.SourceWF env source)
    (Hformation : VInductDecl.OrdinaryFormationWF env source)
    (Hmodel : s.Models env source)
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfam : s.FamilyTypesWF (envCtors.addProjections source.projectionEntries) source.uvars)
    (htypes : block.types = source.typeConstants)
    (hctors : block.ctors = source.constructorConstants)
    (hprojections : block.projections = source.projectionEntries) :
    CaseCompilationData env source source s [] block where
  sourceWF := Hsource
  sourceParameters := Hformation.sourceParameterWF
  expandedWF := Hsource
  headerPrefix := (List.take_of_length_le (by simp [VInductDecl.typeConstants])).symm
  expandedFormation := Hformation
  model := Hmodel
  uvars := rfl
  nparams := rfl
  safety := rfl
  restorationScoped := by
    simp [show compilationRestoration source [] = {} from rfl, Restoration.Scoped]
  correspondence := by
    refine ⟨envTypes, [], hadded, rfl, ?_, ?_⟩
    · simp
    · simpa only [show compilationRestoration source [] = {} from rfl, List.append_nil] using
        Hmodel.restores_empty Hformation.sourceParameterWF hadded
  familyTypesWF := ⟨envTypes, envCtors, hadded, hctorsAdded, hfam⟩
  types := htypes
  ctors := hctors
  projections := hprojections

theorem recursorNamesFresh_nil {env : VEnv} {source expanded : VInductDecl} :
    RecursorNamesFresh env source expanded [] := by
  intro n hn
  simp [compilationRestoration] at hn

end Lean4Lean.InductiveSignature
