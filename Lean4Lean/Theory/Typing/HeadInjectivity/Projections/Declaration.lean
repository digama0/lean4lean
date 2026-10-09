import Lean4Lean.Theory.Typing.EnvLemmas

/-! # The declaration of a projection entry in the declaration history

Every projection entry of an environment in the history `VEnv.WF'` is the entry of a
single-constructor family of an inductive declaration `decl`. The entry is installed, either
by the `induct` declaration or by an `inductProjections` step, on top of an earlier
environment `base` of the history. The constructor's type is well formed in
`envTypes = base.addConstVals decl.typeConstants`. That environment has the rules,
projections and eliminators of `base`, so soundness of `base`'s derivations applies to it.
-/

namespace Lean4Lean

/-- The facts recorded at the installation of a projection entry, at the header environment
`envTypes` in which its family and constructor were checked. -/
def VEnv.ProjDeclAt (env envTypes : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  ∃ (base : VEnv) (dsb : List VDecl) (decl : VInductDecl) (type : VInductiveType)
    (ctor : VConstVal),
    base.WF' dsb ∧ base.addConstVals decl.typeConstants = some envTypes ∧ envTypes ≤ env ∧
    envTypes.Ordered ∧ type ∈ decl.types ∧ type.ctors = [ctor] ∧ type.name = S ∧
    info.uvars = decl.uvars ∧ info.nparams = decl.nparams ∧ info.nindices = type.numIndices ∧
    info.resultLevel = type.resultLevel ∧ info.ctorName = ctor.name ∧ info.ctorType = ctor.type ∧
    ctor.uvars = decl.uvars ∧ envTypes.IsType decl.uvars [] ctor.type ∧
    decl.RawCtorShape type ctor ∧ decl.sourceNames.Nodup ∧ decl.SourceParameterWF base

/-- The facts recorded at the installation of a projection entry, at some header
environment (`VEnv.ProjDeclAt`). -/
def VEnv.ProjDecl (env : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  ∃ envTypes, env.ProjDeclAt envTypes S info

theorem VEnv.ProjDeclAt.origin {env envTypes : VEnv} {S : Name} {info : VProjectionInfo}
    (h : env.ProjDeclAt envTypes S info) : env.ProjDecl S info := ⟨_, h⟩

end Lean4Lean

namespace Lean4Lean

theorem VExpr.mkApps_getAppFnArgs_go : ∀ (e : VExpr) (args : List VExpr),
    VExpr.mkApps (VExpr.getAppFnArgs.go e args).1 (VExpr.getAppFnArgs.go e args).2 =
      VExpr.mkApps e args
  | .app f a, args => by
    rw [show VExpr.getAppFnArgs.go (.app f a) args = VExpr.getAppFnArgs.go f (a :: args) from rfl,
      VExpr.mkApps_getAppFnArgs_go f (a :: args)]
    rfl
  | .bvar .., _ | .sort .., _ | .const .., _ | .elim .., _ | .proj .., _ | .lam .., _
  | .forallE .., _ => rfl

/-- **The syntactic shape of a projection-registered constructor type**: a telescope ending
in the family at its own universe parameters, applied to the parameter variables and to index
arguments. -/
theorem VEnv.ProjDecl.ctorType_shape {env : VEnv} (h : env.ProjDecl S info) :
    ∃ doms idx, info.ctorType = VExpr.wrapForalls doms
        (VExpr.mkApps (.const S (VLevel.params info.uvars))
          ((List.range info.nparams).reverse.map
              (fun i => .bvar (doms.length - info.nparams + i)) ++ idx)) ∧
      info.nparams ≤ doms.length ∧ idx.length = info.nindices := by
  obtain ⟨-, -, -, decl, type, ctor, -, -, -, -, htype, -, rfl, hu, hnp, hni, -, -, hct, -, -, hraw,
    hnodup, -⟩ := h
  obtain ⟨doms, result, heq, hle, ⟨type', hmem', htarget, levels, hfn, -, hargs, htake⟩, hhead⟩ :=
    hraw
  have hname : type.name = type'.name := by
    rcases htarget with h | h
    · cases h
    · exact Option.some.inj h
  have htt : type' = type := VInductDecl.type_eq_of_mem_name hnodup hmem' htype hname.symm
  subst htt
  have htake' : result.getAppFnArgs.2.take decl.nparams =
      decl.paramVars (doms.length - decl.nparams) := htake
  have hargs' : result.getAppFnArgs.2.length = decl.nparams + type'.numIndices := hargs
  have hres := VExpr.mkApps_getAppFnArgs result
  rw [hhead, ← List.take_append_drop decl.nparams result.getAppFnArgs.2, htake'] at hres
  refine ⟨doms, result.getAppFnArgs.2.drop decl.nparams, ?_, by omega, ?_⟩
  · rw [hct, heq, hu, hnp]
    conv => lhs; rw [← hres]
    rfl
  · simp [hargs', hni]

/-- Every single-constructor family of a declaration has a projection entry. -/
theorem VInductDecl.mem_projectionEntries {decl : VInductDecl} {ty : VInductiveType}
    {ctor : VConstVal} (htype : ty ∈ decl.types) (hctors : ty.ctors = [ctor]) :
    VProjectionEntry.mk ty.name (VProjectionInfo.mk decl.uvars decl.nparams ty.numIndices
        ty.resultLevel ctor.name ctor.type) ∈
      decl.projectionEntries := by
  simp only [VInductDecl.projectionEntries, List.mem_filterMap]
  exact ⟨ty, htype, by rw [hctors]⟩

end Lean4Lean
