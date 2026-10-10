import Lean4Lean.Theory.VDecl

/-! # The staged extension `VEnv.addInduct` and the recursor data of a compiled block

The stages of `VEnv.addInduct` (type formers, constructors, projections, recursors, ι rules)
and the syntactic reading of a declaration's recursors off a compiled block
(`VRecRule.OfEquation`, `VInductDecl.RecsOf`). Moved here from `Theory/Inductive.lean` so
that `Theory/Inductive/Compilation.lean` can phrase the installation of a prior container
(`ContainersInstalled`) on `addInduct` (`-- WAVE 2 COMPAT`). -/

namespace Lean4Lean

/-- Register recursor rule `ru` (of recursor `r`) as an ι rule: redex `r`'s spine (major
at `getMajorIdx`) applied to `ru.ctor`'s spine (`ctorParams + nfields` arguments),
reduct `SimplePattern.iotaRHS`. Fails if `ru.rhs` is not closed. Only the constructor
rule of thesis §2.6.4 is registered: K-like reduction (its second rule, on a
non-constructor major of a subsingleton eliminator) is not registered — see
`VInductDecl.WF`. -/
def VEnv.addRecRule (env : VEnv) (r : VRecursor) (ru : VRecRule) : Option VEnv :=
  if h : ru.rhs.Closed then
    some <| env.addPat
      (SimplePattern.iota r.name (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs h,
        .true)
  else none

/-! ### The stages of `addInduct`

The kernel (`Inductive/Add.lean`, `run`) declares all type formers, then all constructors
(in block order), then each recursor *together with its rules* (`mkRecRules` inside the
per-recursor loop, installed in one `recInfo`); for a nested block `Environment.addInductive`
inserts type by type (`Verify/Environment/Basic.lean`, `AddInduct.consts`). The model
re-groups this into five stages — all type formers, all constructors, the projection entries
of the block's structures, all recursors, then all ι rules — which yields the same resulting
environment as the kernel's interleaving, not its literal order. Each stage is
named so that `VInductDecl.WF` can type each kind of constant in the environment the kernel
checks it in. -/

/-- Stage 0: add the type formers as constants. -/
def VInductDecl.addTypes (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.types.foldlM (init := env) fun e t => e.addConst t.name t.toVConstVal.toVConstant

/-- Stage 1: add the constructors of every type former, in block order. -/
def VInductDecl.addCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.types.flatMap (·.ctors)).foldlM (init := env) fun e c => e.addConst c.name c.toVConstant

/-- Stage 2: register the projection entries of the declaration's structures
(`VInductDecl.projectionEntries`). Total: projection registration cannot fail. The recursors
are checked in the resulting environment, where the block's structures already have their
projections (the checker may apply `structEta`, `unitLike` or project out of them while
checking the generated recursor types). -/
def VInductDecl.addProjs (decl : VInductDecl) (env : VEnv) : VEnv :=
  env.addProjections decl.projectionEntries

/-- Stage 3: add the recursors as constants. -/
def VInductDecl.addRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r => e.addConst r.name r.toVConstVal.toVConstant

/-- Stage 4: register every recursor rule as an ι rule. -/
def VInductDecl.addRules (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru

/-- Stages 0–1: the constructor environment. -/
def VInductDecl.addTypesCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypes env >>= decl.addCtors

/-- Stages 0–2: the environment the recursors are checked in. -/
def VInductDecl.addTypesCtorsProjs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.addTypesCtors env).map decl.addProjs

/-- Stages 0–3: the environment the ι rules are registered in. -/
def VInductDecl.addTypesCtorsProjsRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypesCtorsProjs env >>= decl.addRecs

/-- The constants of the declaration as `(name, constant)` pairs, in stage order (type
formers, constructors, recursors): the constant stages are the `addConst` fold over this list
(`VInductDecl.addTypesCtorsProjsRecs_eq`). -/
def VInductDecl.consts (decl : VInductDecl) : List (Name × VConstant) :=
  decl.types.map (fun t => (t.name, t.toVConstVal.toVConstant)) ++
  (decl.types.flatMap (·.ctors)).map (fun c => (c.name, c.toVConstant)) ++
  decl.recs.map (fun r => (r.name, r.toVConstVal.toVConstant))

/-- Extend `env` with the type formers, constructors, and recursors of `decl` (as
constants), the projection entries of its structures (as `projections`) and its
ι-reduction rules (as `pats`), or `none` on a name clash or a non-closed rule reduct. The
chain of `VInductDecl.addTypes`, `addCtors`, `addProjs`, `addRecs`, `addRules`. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.addTypesCtorsProjsRecs env >>= decl.addRules


/-- Stage 0 of `addInduct` is `addConstVals` over the type constants. -/
theorem VInductDecl.addTypes_eq_addConstVals (decl : VInductDecl) (env : VEnv) :
    decl.addTypes env = env.addConstVals decl.typeConstants := by
  unfold VInductDecl.addTypes VInductDecl.typeConstants
  induction decl.types generalizing env with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldlM_cons, List.map_cons, VEnv.addConstVals]
    cases env.addConst t.name t.toVConstVal.toVConstant <;> simp [ih]

/-- Stage 1 of `addInduct` is `addConstVals` over the constructor constants. -/
theorem VInductDecl.addCtors_eq_addConstVals (decl : VInductDecl) (env : VEnv) :
    decl.addCtors env = env.addConstVals decl.constructorConstants := by
  unfold VInductDecl.addCtors VInductDecl.constructorConstants
  generalize decl.types.flatMap (·.ctors) = cs
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldlM_cons, VEnv.addConstVals]
    cases env.addConst c.name c.toVConstant <;> simp [ih]


/-- `decl.recs` is read off a compiled block: the recursor constants are the block's
generated recursors, in order, and each recursor rule is the block's generated equation
for that recursor and constructor, reduct for reduct (`VRecRule.OfEquation`). -/
def VRecRule.OfEquation (r : VRecursor) (ru : VRecRule) (df : VDefEq) : Prop :=
  df.rhs = ru.rhs ∧
  df.lhs.lamBody.headConst? = some r.name ∧
  df.lhs.lamBody.getAppArgs.length = r.getMajorIdx + 1 ∧
  ∃ major, df.lhs.lamBody.getAppArgs.getLast? = some major ∧
    major.headConst? = some ru.ctor ∧
    major.getAppArgs.length = ru.ctorParams + ru.nfields

/-- The recursor data of a declaration against a compiled block: the recursor constants are
the block's, and the rules are in bijection with the block's generated equations. -/
structure VInductDecl.RecsOf (decl : VInductDecl) (block : VInductBlock) : Prop where
  recursors : decl.recs.map (·.toVConstVal) = block.recursors
  rules : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ df ∈ block.rules, VRecRule.OfEquation r ru df
  rules_total : ∀ df ∈ block.rules, ∃ r ∈ decl.recs, ∃ ru ∈ r.rules, VRecRule.OfEquation r ru df

end Lean4Lean
