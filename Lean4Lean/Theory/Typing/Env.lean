import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | mutualDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env →
    env.addInduct decl = some env' →
    VDecl.WF env (.induct decl) env'

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  /-- The projection stage of an inductive declaration (`VInductDecl.addProjs`): register
  the projection entries of a declaration whose type formers and constructors are present
  and well formed, before its recursors are checked. The checker runs that happen in the
  recursor-checking environment therefore run in a well-formed environment, which every
  checker theorem requires. Both the source base and the constructor-complete environment
  retain declaration traces; the remaining premises tie the new metadata to that precise
  prefix (they are what `Ordered.projectionShape` reads off a registered entry). -/
  | inductProjections {base envTypes envCtors : VEnv}
      {decl : VInductDecl} {block : VInductBlock} :
    VEnv.WF' baseDecls base →
    VEnv.WF' ds envCtors →
    decl.sourceNames.Nodup →
    (∀ type ∈ decl.types, type.toVConstant.WF base) →
    (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) →
    (∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes) →
    decl.SourceParameterWF base →
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor) →
    block.types = decl.typeConstants →
    block.ctors = decl.constructorConstants →
    block.projections = decl.projectionEntries →
    base.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    VEnv.WF' ds (envCtors.addProjections block.projections)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/-- Register the projection table of one exact inductive prefix before its
recursors are installed. -/
theorem VEnv.WF.inductProjections
    {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock}
    (hbase : base.WF) (hctorsWF : envCtors.WF)
    (hsource : decl.sourceNames.Nodup)
    (htypesWF : ∀ type ∈ decl.types, type.toVConstant.WF base)
    (hconstructorUvars :
      ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hctorsWF' : ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes)
    (hparams : decl.SourceParameterWF base)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addProjections block.projections).WF := by
  rcases hbase with ⟨baseDecls, hbase⟩
  rcases hctorsWF with ⟨decls, hctorsWF⟩
  exact ⟨decls, .inductProjections hbase hctorsWF hsource htypesWF
    hconstructorUvars hctorsWF' hparams hshape htypesSource hctorsSource hprojections
    htypes hctors⟩

/-- `env₀` is the environment reached by a prefix of `env`'s declaration list: `env` extends
`env₀` by a run of well-formed declarations. The environments the strengthening argument
walks through (`VEnv.WF.strong`) are these and their extensions by constants alone. -/
inductive VEnv.WFPrefix : VEnv → VEnv → Prop where
  | rfl : VEnv.WFPrefix env env
  | decl {d} : VDecl.WF env d env' → VEnv.WFPrefix env env₀ → VEnv.WFPrefix env' env₀
  /-- The projection stage of an inductive declaration (`VEnv.WF'.inductProjections`) is a
  step of the history too. -/
  | projs {entries : List VProjectionEntry} :
    VEnv.WFPrefix env env₀ → VEnv.WFPrefix (env.addProjections entries) env₀

/-- A prefix of a prefix is a prefix. -/
theorem VEnv.WFPrefix.trans {env env₁ env₂ : VEnv}
    (h₁ : env.WFPrefix env₁) (h₂ : env₁.WFPrefix env₂) : env.WFPrefix env₂ := by
  induction h₁ with
  | rfl => exact h₂
  | decl hd _ ih => exact .decl hd (ih h₂)
  | projs _ ih => exact .projs (ih h₂)
