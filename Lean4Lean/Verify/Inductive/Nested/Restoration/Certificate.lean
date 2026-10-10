import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorationRun
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Verify.Inductive.Nested.Restoration.Run

/-! # The restored block: the certificate of a nested restoration

`RestoredBlock L sourceTypes isUnsafe outEnv` is what the restoration of a lowered run `L`
certifies about the returned environment `outEnv`, in the foundation's vocabulary (frozen
interface of the wave 3 scaffold; the Restoration owners produce it, `Nested/Restoration/Restore.lean`,
the Equations owner adds the rule typing, `Nested/Equations/Rules.lean`, the Install owner
reads it, `Nested/Install/**`):

* the **source declaration** `decl` with the restored recursors (the source families' with
  their restored rules, the auxiliary recursors renamed `Main.rec_k` firing on the containers'
  constructors), its translation from the submitted source syntax (`TrInductDeclCore`), its
  nested formation (`NestedFormationWF`, through the lowered declaration `L.loweredDecl`);
* the **compilation**: the specialization list `auxiliaries` (the auxiliary families as
  parameter specializations of containers installed below, `ContainersInstalled` on
  `addInduct`), the compilation data of the lowered run's generator with the restoration table
  `compilationRestoration decl auxiliaries` (`CompilationData`: the restored recursors are the
  restored generated recursors, the restored rules the restored generated equations), and the
  reading of `decl.recs` off that block (`RecsOf`);
* the **kernel constants** (`ivals`, `rvals`), their translations (`TrIndType`, `TrRecursor` in
  the stages of `VEnv.addInduct`), the kernel insertion order and the output constant map
  (`order`, `map_eq`, `fresh`, `newUnsafe`);
* the **shape clauses** of `VInductDecl.WF` for the restored recursors (`recs_wf`, `rec_shape`,
  `rules_nodup`, `rules_ctor` on the container's or the block's constructors, `rule_shape`,
  `rules_closed`) and the facts recursor reduction reads of the new recursors in the output
  model (`recShapes`, `recK`), auxiliary recursors included.

What is *not* here is the typing of the restored rules (`VInductDecl.WF.rules_wf`,
`RestoredBlock.rulesWF`) and of the restored block's equations (`RestoredBlock.blockWF`): they
go through the restoration interpretation (`Theory/Inductive/RestorationInterpretation.lean`)
and are the Equations owner's (`Nested/Equations/Rules.lean`). `RestoredBlock.addInduct` and
`RestoredBlock.wf` (given those two) are proved here. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The certificate of a nested restoration (see the module documentation). -/
structure RestoredBlock {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {res : ElimNestedInductive.Result} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams res.types.toArray loweredEnv)
    (sourceTypes : List InductiveType) (isUnsafe : Bool) (outEnv : Environment) where
  /-- The source declaration, with the restored recursors. -/
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  /-- The exact source syntax translates to `decl` (headers in the source model, constructors
  in the header stage). -/
  source : TrInductDeclCore Hc.venv c.lparams nparams sourceTypes isUnsafe decl envTypes envCtors
  /-- Nested formation of the source declaration, through the lowered declaration. -/
  formation : decl.NestedFormationWF Hc.venv
  /-- The auxiliary families as parameter specializations of installed containers. -/
  auxiliaries : List ContainerSpecialization
  containers : ContainersInstalled Hc.venv auxiliaries
  /-- The restored block of the lowered run's generator. -/
  block : VInductBlock
  compiled : CompilationData Hc.venv decl L.loweredDecl L.recursors.signature
    L.recursors.generation auxiliaries block
  /-- `decl.recs` is read off the restored block. -/
  recsOf : decl.RecsOf block
  /-- The kernel constants: the restored headers and constructors (`all := the source names`),
  the restored recursors. -/
  ivals : List (InductiveVal × List ConstructorVal)
  rvals : List RecursorVal
  trTypes : List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
    TrIndType c.safety Hc.venv envTypes iv.1 iv.2 t) ivals decl.types
  /-- The recursor stage. -/
  envR : VEnv
  recsAdded : decl.addRecs (decl.addProjs envCtors) = some envR
  trRecs : List.Forall₂ (TrRecursor c.safety (decl.addProjs envCtors) envR outEnv.constants)
    rvals decl.recs
  /-- The kernel's insertion order (per source family: header, constructors, recursor; then the
  auxiliary recursors). -/
  order : List ConstantInfo
  order_perm : order.Perm (AddInduct.consts ivals rvals)
  fresh : ∀ ci ∈ AddInduct.consts ivals rvals, c.env.constants.find? ci.name = none
  map_eq : outEnv.constants = insertConsts c.env.constants order
  quotInit_eq : outEnv.quotInit = c.env.quotInit
  newUnsafe : ∀ ci ∈ AddInduct.consts ivals rvals, ci.isUnsafe = isUnsafe
  /-- `VInductDecl.WF.recs_wf` in the projection stage. -/
  recs_wf : ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF (decl.addProjs envCtors)
  /-- `VInductDecl.WF.rec_shape`. -/
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- `VInductDecl.WF.rules_nodup`. -/
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  /-- `VInductDecl.WF.rules_ctor` in the constructor stage: the block's own constructors for the
  source recursors, the container's (declared below) for the auxiliary ones. -/
  rules_ctor : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∃ ci, envCtors.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  /-- `VInductDecl.WF.rule_shape`. -/
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  /-- Every restored reduct is closed, so the rule stage succeeds. -/
  rules_closed : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed
  /-- The output model: the rule stage. -/
  outVEnv : VEnv
  rulesAdded : decl.addRules envR = some outVEnv
  /-- The recursor and constructor telescopes of every new recursor (auxiliary recursors
  included: their majors are containers at the specialized arguments), for
  `InstalledBlocks.addInduct`'s `hrecShapes`. -/
  recShapes : ∀ rval ∈ rvals, RecursorShapesAt outEnv.constants outVEnv rval
  /-- The K clause of every new recursor. -/
  recK : ∀ rval ∈ rvals, KLikeRecursor outEnv.constants outVEnv rval
  /-- (Added by Restoration-B.) The run object of the source branch (`NestedRun`), from which
  the restoration certificates are read (the Equations owner's restoration substitution, the
  Install owner's kernel facts). Its lowered run is `L`'s view. -/
  run : NestedRun res c.env sourceTypes Hc.venv decl c.lparams nparams isUnsafe c.safety outEnv
  run_loweredEnv : run.loweredEnv = loweredEnv
  run_lowered : HEq run.lowered L.view

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The projection stage. -/
abbrev envP (B : RestoredBlock L sourceTypes isUnsafe outEnv) : VEnv :=
  B.decl.addProjs B.envCtors

theorem stT (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.decl.addTypes Hc.venv = some B.envTypes := by
  rw [VInductDecl.addTypes_eq_addConstVals]; exact B.source.typesAdded

theorem stC (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.decl.addCtors B.envTypes = some B.envCtors := by
  rw [VInductDecl.addCtors_eq_addConstVals]; exact B.source.ctorsAdded

/-- PR #43's step witness, assembled from the stages. -/
def addInduct (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    AddInduct c.safety c.env.constants Hc.venv B.decl outEnv.constants B.outVEnv where
  ivals := B.ivals
  rvals := B.rvals
  envT := B.envTypes
  envC := B.envCtors
  envR := B.envR
  stT := B.stT
  stC := B.stC
  stR := B.recsAdded
  stP := B.rulesAdded
  types := B.trTypes
  recs := B.trRecs
  order := B.order
  order_perm := B.order_perm
  fresh := B.fresh
  map_eq := B.map_eq

theorem installed (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    Hc.venv.addInduct B.decl = some B.outVEnv :=
  B.addInduct.env_eq

theorem le (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Hc.venv ≤ B.outVEnv :=
  B.addInduct.le

theorem isUnsafe_eq (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.decl.isUnsafe = isUnsafe :=
  B.source.isUnsafe

theorem types_ne_nil (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsource : sourceTypes ≠ []) : B.decl.types ≠ [] :=
  TrInductDeclCore.nonempty B.source hsource

/-- The compilation of the source declaration. -/
theorem compilesTo (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.decl.CompilesTo Hc.venv B.block :=
  .intro B.compiled B.containers

theorem recsCompiled (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.decl.RecsCompiled Hc.venv :=
  ⟨B.block, B.compilesTo, B.recsOf⟩

/-- (For the model's `PatValid.iota`.) Every installed rule is `OfEquation` of a block
equation that is the restoration of a generated equation of the lowered run's generator
(`CompilationData.equations`). -/
theorem rules_ofRestoredEquation (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    {r : VRecursor} {ru : VRecRule} (hr : r ∈ B.decl.recs) (hru : ru ∈ r.rules) :
    ∃ df ∈ B.block.rules, VRecRule.OfEquation r ru df ∧
      ∃ k, (compilationRestoration B.decl B.auxiliaries).equation
        (L.recursors.generation.equation k) = some df := by
  obtain ⟨df, hdf, hof⟩ := B.recsOf.rules r hr ru hru
  refine ⟨df, hdf, hof, ?_⟩
  have h := B.compiled.equations
  unfold Instance.restoredEquations at h
  obtain ⟨eq, heq, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp h) df hdf
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp heq
  exact ⟨k, hrestore⟩

/-- (For `WF.patCtor_rigid`.) The constructor of every restored rule is a constructor of the
source declaration or of a registered ι rule of the source model (a container's). -/
theorem rule_ctor_cases (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    {r : VRecursor} {ru : VRecRule} (hr : r ∈ B.decl.recs) (hru : ru ∈ r.rules) :
    (∃ ctor ∈ B.decl.constructorConstants, ru.ctor = ctor.name) ∨ VEnv.IsPatCtor Hc.venv ru.ctor :=
  B.compilesTo.rule_ctor_cases B.recsOf hr hru

/-- `VInductDecl.WF` of the restored declaration, given the typing of its rules
(`RestoredBlock.rulesWF`, `Nested/Equations/Rules.lean`). -/
theorem wf (B : RestoredBlock L sourceTypes isUnsafe outEnv) (hsource : sourceTypes ≠ [])
    (hrules : ∀ r ∈ B.decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      B.envR.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor r.numParams r.numMotives r.numMinors
          r.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true)) :
    B.decl.WF Hc.venv where
  source := TrInductDeclCore.sourceWF_ofNonempty B.source (B.types_ne_nil hsource)
  formation := .nested B.formation VEnv.LE.rfl
  recsCompiled := B.recsCompiled
  recs_wf envP hP r hr := by
    have := B.addInduct.addTypesCtorsProjs
    rw [hP] at this
    cases this
    exact B.recs_wf r hr
  rec_shape := B.rec_shape
  rules_nodup := B.rules_nodup
  rules_ctor envC hC := by
    have := B.addInduct.addTypesCtors
    rw [hC] at this
    cases this
    exact B.rules_ctor
  rule_shape := B.rule_shape
  rules_wf envR hR := by
    have := B.addInduct.addTypesCtorsProjsRecs
    rw [hR] at this
    cases this
    exact hrules

end RestoredBlock
end VerifyInductive
end Lean4Lean
