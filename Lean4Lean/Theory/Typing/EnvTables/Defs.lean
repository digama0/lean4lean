import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseRegistration

/-!
# Environment tables: definitions and the history invariant

The observation model (`Theory/Typing/HeadInjectivity/Model/`) needs, for an arbitrary `VEnv.WF`
environment, a constructor table and a family table, together with a classification of every
stored equation. These are not functions of the final environment alone: the same axiomatized
constants can be described by two declarations with different parameter counts (see
`EnvTables/OfWF.lean` for the counterexample), so the tables are built along the declaration history,
recording the *first* registration ("view") of every family. This file defines the tables, the
history invariant `Tables.Inv`, and proves that every `VEnv.WF'` history has tables satisfying it.

Only the uniqueness-free base is imported.
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

variable {env env' : VEnv}

/-- Constructor metadata: owning family, universe arity, parameter and field counts. -/
structure CtorData where
  family : Name
  uvars : Nat
  nparams : Nat
  nfields : Nat
  deriving DecidableEq

/-- Family metadata: universe arity, parameter and index counts, result level, and the
constructors in declaration order. -/
structure FamData where
  uvars : Nat
  nparams : Nat
  nindices : Nat
  resultLevel : VLevel
  ctors : List Name

/-- The view of family `type` given by declaration `decl`. -/
def famView (decl : VInductDecl) (type : VInductiveType) : FamData :=
  ⟨decl.uvars, decl.nparams, type.numIndices, type.resultLevel, type.ctors.map (·.name)⟩

/-- The view of constructor `ctor` of family `type` given by declaration `decl`: the fields are
the syntactic binders of the constructor type after the parameters. -/
def ctorView (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal) : CtorData :=
  ⟨type.name, decl.uvars, decl.nparams, ctor.type.forallArity - decl.nparams⟩

def quotFam : FamData := ⟨1, 2, 0, .param 0, [``Quot.mk]⟩
def quotCtor : CtorData := ⟨``Quot, 1, 2, 1⟩

/-- The family entry of a registered projection (structure) entry. -/
def projFam (info : VProjectionInfo) : FamData :=
  ⟨info.uvars, info.nparams, info.nindices, info.resultLevel, [info.ctorName]⟩

/-- The constructor entry of a registered projection (structure) entry. -/
def projCtor (typeName : Name) (info : VProjectionInfo) : CtorData :=
  ⟨typeName, info.uvars, info.nparams, info.numFields⟩

/-- The syntactic shape of a constructor of the table (`VConstructorShape` of
`Theory/Typing/RecursorLemmas.lean`, with `vars n m = bvarRange n (n + m)`). -/
def CtorShape (env : VEnv) (c : Name) (k : CtorData) : Prop :=
  ∃ ci doms indices, env.constants c = some ci ∧ ci.uvars = k.uvars ∧
    ci.type = VExpr.wrapForalls doms (VExpr.mkApps (.const k.family (VLevel.params k.uvars))
      (vars k.nparams k.nfields ++ indices)) ∧
    doms.length = k.nparams + k.nfields

/-- The (typed, not syntactic) shape of a family of the table: its type is definitionally a
telescope of `nparams + nindices` binders ending in the recorded sort. -/
def FamShape (env : VEnv) (I : Name) (d : FamData) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ci.uvars = d.uvars ∧
    ∃ doms result type, env.IsDefEq d.uvars [] ci.type (VExpr.wrapForalls doms result) type ∧
      doms.length = d.nparams + d.nindices ∧
      env.IsDefEq d.uvars doms.reverse result (.sort d.resultLevel) (.sort d.resultLevel.succ)

theorem CtorShape.mono (H : CtorShape env c k) (hle : env ≤ env') : CtorShape env' c k := by
  obtain ⟨ci, doms, indices, h1, h2, h3, h4⟩ := H
  exact ⟨ci, doms, indices, hle.constants h1, h2, h3, h4⟩

theorem FamShape.mono (H : FamShape env I d) (hle : env ≤ env') : FamShape env' I d := by
  obtain ⟨ci, h1, h2, doms, result, type, h3, h4, h5⟩ := H
  exact ⟨ci, hle.constants h1, h2, doms, result, type, h3.mono hle, h4, h5.mono hle⟩

/-! ## Constant occurrences -/

/-- `e` contains a literal occurrence of the constant `X`. -/
def Mentions (X : Name) : VExpr → Prop
  | .const n _ => n = X
  | .app f a | .lam f a | .forallE f a => Mentions X f ∨ Mentions X a
  | .proj _ _ e => Mentions X e
  | _ => False

theorem Mentions.mkApps_fn (h : Mentions X f) : Mentions X (VExpr.mkApps f args) := by
  induction args generalizing f with
  | nil => exact h
  | cons a args ih => exact ih (f := .app f a) (Or.inl h)

theorem Mentions.mkApps_head : Mentions X (VExpr.mkApps (.const X ls) args) :=
  Mentions.mkApps_fn (show Mentions X (.const X ls) from rfl)

/-! ## The tables -/

/-- The source constructor names of a certified schema, as determined by the schema. -/
def schemaCtorNames (schema : CaseSchema) : List Name :=
  (schema.signature.declaration.types.take schema.sourceFamilies.length).flatMap
    fun type => type.ctors.map (·.name)

/-- Metadata witnessing that a table entry is declared in every well-formed environment
below the current one with the same equations, projections and eliminators. -/
def MetadataMentions (env : VEnv) (X : Name) : Prop :=
  (∃ df, env.defeqs df ∧ Mentions X df.lhs) ∨
  (∃ df Y ci, env.defeqs df ∧ Mentions Y df.lhs ∧ env.constants Y = some ci ∧
    Mentions X ci.type) ∨
  (∃ s info, env.projections s info ∧ (X = s ∨ X = info.ctorName)) ∨
  (∃ key schema, env.eliminators key schema ∧
    (X ∈ schema.sourceFamilies ∨ X ∈ schemaCtorNames schema))

theorem MetadataMentions.mono (H : MetadataMentions env X) (hle : env ≤ env') : MetadataMentions env' X := by
  rcases H with ⟨df, h1, h2⟩ | ⟨df, Y, ci, h1, h2, h3, h4⟩ | ⟨s, info, h1, h2⟩ |
    ⟨key, schema, h1, h2⟩
  · exact .inl ⟨df, hle.defeqs h1, h2⟩
  · exact .inr <| .inl ⟨df, Y, ci, hle.defeqs h1, h2, hle.constants h3, h4⟩
  · exact .inr <| .inr <| .inl ⟨s, info, hle.projections h1, h2⟩
  · exact .inr <| .inr <| .inr ⟨key, schema, hle.eliminators h1, h2⟩

structure Tables where
  defs : Name → Option VDefVal
  recursors : Name → Option RecursorData
  quot : Bool
  fam : Name → Option FamData
  ctor : Name → Option CtorData

/-- `T'` extends `T`: no entry is removed or changed. -/
structure Tables.Extends (T T' : Tables) : Prop where
  defs : T.defs n = some v → T'.defs n = some v
  recursors : T.recursors n = some d → T'.recursors n = some d
  quot : T.quot = true → T'.quot = true
  fam : T.fam n = some f → T'.fam n = some f
  ctor : T.ctor n = some k → T'.ctor n = some k

theorem Tables.Extends.rfl {T : Tables} : T.Extends T := ⟨id, id, id, id, id⟩

theorem Tables.Extends.trans {T₁ T₂ T₃ : Tables} (h₁ : T₁.Extends T₂) (h₂ : T₂.Extends T₃) :
    T₁.Extends T₃ :=
  ⟨h₂.defs ∘ h₁.defs, h₂.recursors ∘ h₁.recursors, h₂.quot ∘ h₁.quot, h₂.fam ∘ h₁.fam,
    h₂.ctor ∘ h₁.ctor⟩

/-- The quotient constants and equation are installed with their exact values. -/
structure QuotInstalled (env : VEnv) : Prop where
  quot : env.constants ``Quot = quotConst
  mkConst : env.constants ``Quot.mk = quotMkConst
  lift : env.constants ``Quot.lift = quotLiftConst
  ind : env.constants ``Quot.ind = quotIndConst
  equation : env.defeqs quotDefEq

theorem QuotInstalled.mono (H : QuotInstalled env) (hle : env ≤ env') : QuotInstalled env' :=
  ⟨hle.constants H.quot, hle.constants H.mkConst, hle.constants H.lift, hle.constants H.ind,
    hle.defeqs H.equation⟩

/-- The installation of a recursor entry: the finite compilation of the very block that
installed it, together with the family views it recorded. -/
def RecursorEntryCompiled (env : VEnv) (T : Tables) (data : RecursorData) : Prop :=
  ∃ base installBase source expanded auxiliaries block installed,
    CompilationData base source expanded data.schema.signature data.recursorInstance
      auxiliaries block ∧
    ContainersInstalled base auxiliaries ∧
    base ≤ installBase ∧
    data.schema.restoration = compilationRestoration source auxiliaries ∧
    data.schema.sourceFamilies = source.types.map (·.name) ∧
    block.install installBase = some installed ∧ installed ≤ env ∧
    installBase.WF ∧ VInductBlock.WF installBase block ∧
    ∀ type ∈ source.types, type.ctors ≠ [] → T.fam type.name = some (famView source type)

theorem RecursorEntryCompiled.mono (H : RecursorEntryCompiled env T data) (hle : env ≤ env')
    (hT : T.Extends T') : RecursorEntryCompiled env' T' data := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed,
    h1, h2, h3, h4, h5, h6, h7, h9, h10, h8⟩ := H
  exact ⟨base, installBase, source, expanded, auxiliaries, block, installed,
    h1, h2, h3, h4, h5, h6, h7.trans hle, h9, h10, fun type ht hc => hT.fam (h8 type ht hc)⟩

theorem RecursorEntryCompiled.registered (H : RecursorEntryCompiled env T data) :
    RecursorRegistered env data := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed,
    h1, h2, h3, h4, h5, h6, h7, _, _, _⟩ := H
  exact ⟨base, installBase, source, expanded, data.recursorInstance, auxiliaries, block, installed,
    h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-- The family and constructor part of the history invariant. -/
structure ViewInv (env : VEnv) (famT : Name → Option FamData) (ctorT : Name → Option CtorData) :
    Prop where
  /-- Family entries. -/
  fam : famT I = some d → FamShape env I d ∧ d.ctors.Nodup ∧
    ∀ c ∈ d.ctors, ∃ k, ctorT c = some k ∧ k.family = I ∧ k.uvars = d.uvars ∧
      k.nparams = d.nparams
  /-- Constructor entries. -/
  ctor : ctorT c = some k → CtorShape env c k ∧ ∃ d, famT k.family = some d ∧ c ∈ d.ctors
  /-- A family is never a constructor. -/
  fam_ctor : famT n ≠ none → ctorT n = none
  /-- Table entries are rigid. -/
  rigid : famT n ≠ none ∨ ctorT n ≠ none → env.Rigid n
  /-- Table entries are witnessed by metadata. -/
  witness : famT n ≠ none ∨ ctorT n ≠ none → MetadataMentions env n

/-- The history invariant of the tables. -/
structure Tables.Inv (env : VEnv) (T : Tables) : Prop where
  /-- Definition entries. -/
  defs : T.defs n = some v → v.name = n ∧ env.constants n = some v.toVConstant ∧
    env.defeqs v.toDefEq
  /-- Recursor entries, with their actual installation. -/
  recursors : T.recursors n = some data → data.name = n ∧ RecursorEntryCompiled env T data
  /-- The quotient flag. -/
  quot : T.quot = true → QuotInstalled env ∧ T.fam ``Quot = some quotFam ∧
    T.ctor ``Quot.mk = some quotCtor ∧ T.defs ``Quot.lift = none ∧
    T.recursors ``Quot.lift = none ∧ T.defs ``Quot.ind = none ∧ T.recursors ``Quot.ind = none
  /-- Definition and recursor heads are distinct. -/
  defs_recursors : T.defs n ≠ none → T.recursors n = none
  /-- Families and constructors. -/
  views : ViewInv env T.fam T.ctor
  /-- Every stored equation is a definition's delta rule, the quotient rule, or an equation of a
  recursor entry. -/
  equations : env.defeqs df →
    (∃ v, T.defs v.name = some v ∧ df = v.toDefEq) ∨
    (T.quot = true ∧ df = quotDefEq) ∨
    (∃ data, T.recursors data.name = some data ∧
      ∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner ∧
        data.equation index = some df)
  /-- Registered projections are structure views of the tables. -/
  projections : env.projections s info →
    T.fam s = some (projFam info) ∧ T.ctor info.ctorName = some (projCtor s info)

end Lean4Lean.EnvTables
