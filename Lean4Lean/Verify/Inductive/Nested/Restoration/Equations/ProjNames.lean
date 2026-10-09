import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.WF
import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Whnf

/-! Projection-name avoidance of the restored generated equations: fields
`constructorProjNames`, `recursorProjNames` and `equationProjNames` of
`RestorationSubstitutionPremises` (`Nested/Restoration/Equations/WF.lean`).

* Translated syntax projects only out of registered structures
  (`TrExprS.targetProjsRegistered`), and translation maps projection nodes to
  projection nodes, so a projection condition on the source carries over to
  the target (`TrExprS.projNamesOK_of_source`).
* Lowered constructor types (`constructorProjNames`) are translated in the
  lowered header environment, whose projections are those of the base
  environment: base structures, absent from the restorable names.
* Generated recursor types (`recursorProjNames`): the executable recursor type
  satisfies the projection condition `ProjsOK (projAvoidsHeads env E.uniformHeads)`
  (`RecursorConstruction.recursorTypeProjsOK`, the projection component of
  `recursorTypeParamUniform`, which the parameter-uniformity chain itself
  drops). Its translation is the generated recursor type, which hence
  neither projects out of a head (in particular an auxiliary family) nor out
  of anything but a registered structure of the recursor-pass environment (a
  base structure or a lowered family). This leaves no restorable name.
* Generated equations (`equationProjNames`) are built from the same pieces as
  the recursor types (parameters, motives, minor premises, and through those
  the field types, induction-hypothesis binders and indices, and constructor
  indices), so their projection names are among those of any generated
  recursor type (`Instance.equation_projNamesAvoid_of_recursorType`).

* Registered eliminator schemas (`eliminatorProjNames`): certified schemas of
  earlier blocks are checked in expanded environments whose projection tables
  may contain never-installed auxiliary structure families, and the
  executable reuses the auxiliary names `_nested.i` across blocks. So this is
  not a consequence of `Certified`; registration instead certifies that the
  schema projects only out of structures registered at registration time
  (`CaseSchema.ProjNamesRegistered`, a field of `VEnv.WF'.inductEliminators`),
  whence out of base structures (`VEnv.WF.eliminatorsProjNamesRegistered`),
  which are base constants (`eliminatorProjNames_of`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! ### Projection names of abstract terms -/

namespace VExpr

/-! `VExpr.ProjNamesOK` itself is defined in `Theory/Inductive/CaseFormation.lean`,
where registration of case schemas uses it. -/

end VExpr

/-! ### Projection names of translated syntax -/

/-- **Translated syntax projects only out of registered structures.** -/
theorem TrExprS.targetProjsRegistered {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (henv : env.Ordered) (H : TrExprS env Us Δ e e')
    (hΔwf : Δ.WF env Us.length)
    (hΔ : VLCtx.ProjNamesOK (fun s => ∃ info, env.projections s info) Δ) :
    e'.ProjNamesOK (fun s => ∃ info, env.projections s info) := by
  induction H with
  | bvar hfind | fvar hfind => exact hΔ hfind
  | sort _ => trivial
  | const => trivial
  | app _ _ _ _ ihf iha => exact ⟨ihf hΔwf hΔ, iha hΔwf hΔ⟩
  | lam hty _ _ iht ihb =>
    exact ⟨iht hΔwf hΔ, ihb ⟨hΔwf, by rintro _ _ ⟨⟩, hty⟩
      (hΔ.cons VLocalDecl.value_vlam_projNamesOK)⟩
  | forallE hty _ _ _ iht ihb =>
    exact ⟨iht hΔwf hΔ, ihb ⟨hΔwf, by rintro _ _ ⟨⟩, hty⟩
      (hΔ.cons VLocalDecl.value_vlam_projNamesOK)⟩
  | letE hval _ _ _ _ ihv ihb =>
    exact ihb ⟨hΔwf, by rintro _ _ ⟨⟩, hval⟩ (hΔ.cons (d := .vlet _ _) (ihv hΔwf hΔ))
  | lit _ _ ih => exact ih hΔwf hΔ
  | mdata _ ih => exact ih hΔwf hΔ
  | proj _ hproj ih =>
    obtain ⟨_, hty⟩ := hproj
    obtain ⟨info, -, -, -, -, -, -, hinfo, -⟩ :=
      VEnv.HasType.proj_inv henv hΔwf.toCtx hty
    exact ⟨⟨info, hinfo⟩, ih hΔwf hΔ⟩

end Lean4Lean

/-! ### The projection condition along binder closing -/

namespace Lean.LocalDecl

/-- The declaration's type (and, for a `let`, its value) satisfy the
projection condition. -/
def DeclProjsOK (ok : Name → Prop) : LocalDecl → Prop
  | .cdecl _ _ _ ty _ _ => ty.ProjsOK ok
  | .ldecl _ _ _ ty val _ _ => ty.ProjsOK ok ∧ val.ProjsOK ok

theorem ParamUniformIn.declProjsOK {env : Lean.Kernel.Environment} {heads : List Name}
    {params : List Expr} {ls : List Level} {d : LocalDecl}
    (H : d.ParamUniformIn env heads params ls) : d.DeclProjsOK (Lean4Lean.projAvoidsHeads env heads) := by
  cases d with
  | cdecl => exact H.1.2
  | ldecl _ _ _ _ v nd _ => exact ⟨H.1.2, (H.2 v (by cases nd <;> rfl)).2⟩

end Lean.LocalDecl

namespace Lean.Expr

open Lean4Lean

namespace ProjsOK

variable {ok : Name → Prop}

private theorem go_projsOK {isLambda : Bool} {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ d, lctx.find? x = some d ∧ d.DeclProjsOK ok) →
    ∀ {b}, ProjsOK ok b → ProjsOK ok (LocalContext.mkBindingListN.go isLambda lctx l b)
  | [], _, _, H => H
  | x :: l, hx, b, H => by
    obtain ⟨d, hfind, hd⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    refine go_projsOK (fun y hy => hx y (.tail _ hy)) ?_
    cases d with
    | cdecl _ _ _ ty _ _ =>
      simp only [LocalContext.mkBindingList1N, hfind]
      have hty := (show ty.ProjsOK ok from hd).abstractN l.reverse 0
      cases isLambda
      · exact ⟨hty, H⟩
      · exact ⟨hty, H⟩
    | ldecl _ _ _ ty val _ _ =>
      obtain ⟨hty, hval⟩ := (show ty.ProjsOK ok ∧ val.ProjsOK ok from hd)
      simp only [LocalContext.mkBindingList1N, hfind]
      split
      · exact ⟨hty.abstractN _ 0, hval.abstractN _ 0, H⟩
      · exact H.lowerLooseBVars' 1 1

/-- Closing a telescope of free variables whose declarations satisfy the
projection condition keeps the projection condition. -/
theorem mkBinding' {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : ProjsOK ok b)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.DeclProjsOK ok) :
    ProjsOK ok (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  exact go_projsOK (fun y hy => hdecl y (List.mem_reverse.1 hy)) (H.abstractN ys 0)

theorem mkForall' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray) (H : ProjsOK ok b)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.DeclProjsOK ok) :
    ProjsOK ok (lctx.mkForall xs b) := by
  subst hxs
  simpa [LocalContext.mkForall] using H.mkBinding' (isLambda := false) (lctx := lctx) hdecl

theorem mkAppN' {f : Expr} {args : Array Expr} (hf : ProjsOK ok f)
    (hargs : ∀ a ∈ args.toList, ProjsOK ok a) : ProjsOK ok (Lean.mkAppN f args) := by
  rw [Lean.Expr.mkAppN_eq_mkAppList]
  exact mkAppList_iff.2 ⟨hf, hargs⟩

theorem getAppArgs_slice' {e : Expr} (H : ProjsOK ok e) (n : Nat) :
    ∀ a ∈ (e.getAppArgs[n:] : Array Expr).toList, ProjsOK ok a := by
  intro a ha
  rw [Lean4Lean.VerifyInductive.Expr.getAppArgs_slice_toList] at ha
  exact H.of_mem_getAppArgsList (List.mem_of_mem_drop ha)

theorem consumeTypeAnnotationsVerified' {e : Expr} (H : ProjsOK ok e) :
    ProjsOK ok (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList (a := type) (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList (a := type) (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

end ProjsOK

end Lean.Expr

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The bound free-variable arrays of the recursor construction declare their
variables with the projection condition when their recorded binder types satisfy it. -/
theorem FVarArrayBinderTypes.declProjsOK {ok : Name → Prop} {c : AddInductive.Context}
    {xs origins : Array Expr}
    (Ho : FVarArrayBinderTypes c xs origins)
    (hQ : ∀ i, i < xs.size → origins[i]!.ProjsOK ok)
    {fv : FVarId} (hfv : Expr.fvar fv ∈ xs) :
    ∃ d, c.lctx.find? fv = some d ∧ d.DeclProjsOK ok := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hfv
  obtain ⟨D, hD⟩ := Ho.declaration i hi
  have hfvD : D.fvar = fv := by
    have := D.expression.symm.trans hget
    exact (Expr.fvar.inj this)
  subst hfvD
  refine ⟨_, D.declaration, ?_⟩
  show D.type.ProjsOK ok
  rw [hD]; exact hQ i hi

/-- **The projection condition of one induction-hypothesis type** (regions R2
and R3 of `Nested/Restoration/Uniform/Recursors.lean`): the projection component of `InductionHypothesisType.paramUniform`. -/
theorem InductionHypothesisType.projsOK
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfPreservesParamUniform heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : InductionHypothesisType stats recInfos root field type)
    (henv : root.env = env)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.ParamUniformScope env heads params ls P)
    (hfieldP : ∀ fv, field = .fvar fv → P fv) :
    type.ProjsOK (projAvoidsHeads env heads) := by
  have hinference := O.loopInput.inference
  have hnormalization := O.loopInput.normalization
  obtain ⟨fv, hfield, hfvRoot⟩ := O.field_fvar
  have hfvP : P fv := hfieldP fv hfield
  obtain ⟨fieldTarget, hfieldTr⟩ := Rroot.trFVar hfvRoot
  subst hfield
  obtain ⟨inferredTarget, hbelow, _, hinferredTr, hfieldTyping⟩ :=
    getTypeFVarInRecursorContext.WF Rroot hfieldTr _ hinference
  obtain ⟨index, dname, dtype, dbi, dkind, hdecl⟩ := Rroot.findCDecl (fv := fv) (by
    rw [← Rroot.mlctx_wf.tr.fvars_eq, Rroot.lctx_eq]; exact hfvRoot)
  have hty : O.loopInput.inferredType = (LocalDecl.cdecl index fv dname dtype dbi dkind).type := by
    have h := hinference
    rw [AddInductive.getType.run] at h
    simp only [LocalContext.get!, Expr.fvarId!, hdecl, Except.ok.injEq] at h
    exact h.symm
  obtain ⟨jF, hjF, ty₀, hlctxF, htr₀, _⟩ := O.loopInput.checkBase Rroot
  let RF := Rroot.withCheckLCtx (loopUArgsCheckLCtx root O.loopInput.prior)
    ((Rroot.check.below jF hjF).cast hlctxF)
  have hinferredEq : O.loopInput.inferredType = (root.lctx.get! fv).type := by
    have h := hinference.symm.trans (AddInductive.getType.run (.fvar fv) root)
    exact Except.ok.inj h
  have hinferred₀ : TrExprS RF.venv recLparams RF.chk.vlctx
      O.loopInput.inferredType ty₀ := by
    rw [hinferredEq]; exact htr₀
  have hdeclH : (LocalDecl.cdecl index fv dname dtype dbi dkind).ParamUniformIn env heads params ls :=
    hscope.2 fv _ hfvP (by rw [Rroot.lctx_eq]; exact hdecl)
  have hinferredH : O.loopInput.inferredType.ParamUniformIn env heads params ls := by
    rw [hty]
    exact hdeclH.1
  have hfieldPin : (Expr.fvar fv).FVarsIn P := by simpa [FVarsIn] using hfvP
  have hinferredP : O.loopInput.inferredType.FVarsIn P := hbelow P hscope.1 hfieldPin
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨⟨hnormalizedBelow, hnormalizedTr⟩, _, hnormalized₀⟩ :=
    whnfInRecursorContext.dualWF RF hinferredTr hinferred₀ _ hnormalization
  have hnormalizedH : O.loopInput.normalizedType.ParamUniformIn env heads params ls :=
    W.whnf RF henv ⟨_, hinferred₀⟩ hscope hinferredP hinferredH
      hnormalization
  have hnormalizedP : O.loopInput.normalizedType.FVarsIn P :=
    hnormalizedBelow P hscope.1 hinferredP
  obtain ⟨Rcurrent, P', _, _, _, hsc', hexposedH, _, _, hargs, _⟩ :=
    O.loopTrace.paramUniform W hp recursorConsumeTypeAnnotationsCompat henv RF hscope
      hnormalizedTr hinferredType hnormalized₀ hnormalizedH hnormalizedP
  have hargDecls : ∀ x ∈ O.arguments_bound.fvars, ∀ decl,
      O.current.lctx.find? x = some decl → decl.DeclProjsOK (projAvoidsHeads env heads) := by
    intro x hx decl hdecl
    have hxArg : Expr.fvar x ∈ O.args.toList := by
      rw [O.arguments_bound.expressions]
      simpa using hx
    obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
    cases hy
    exact (hsc'.2 x decl hyP (by rw [Rcurrent.lctx_eq]; exact hdecl)).declProjsOK
  obtain ⟨m, hm, _⟩ := O.motive_is_fvar
  rw [O.type_eq]
  refine Expr.ProjsOK.mkForall' O.arguments_bound.expressions ?_ ?_
  · refine ⟨Expr.ProjsOK.mkAppN' (by rw [hm]; trivial) (hexposedH.2.getAppArgs_slice' _),
      Expr.ProjsOK.mkAppN' trivial ?_⟩
    intro a ha
    rw [O.arguments_bound.expressions] at ha
    simp only [List.mem_map] at ha
    obtain ⟨y, -, rfl⟩ := ha
    trivial
  · intro y hy
    have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
    obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
    exact ⟨_, hfind, hargDecls y hy _ hfind⟩

section Assembly

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

namespace RecursorConstruction

variable (H : RecursorConstruction R)

/-- **The projection condition of one generated minor premise type**: the
projection component of `minorParamUniform` (field declarations, induction
hypotheses and the minor's declared type). -/
theorem minorProjsOK {heads : List Name} (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.origins.minorShapes owner howner localIndex hlocal).origin.ProjsOK
      (projAvoidsHeads H.localContext.env heads) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RuleTemplateMatchesMinor stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleTemplates[localIndex]! :=
    H.templates.entry owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.templateTyping.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots Hsem ⊢
  generalize H.recInfos[owner]!.ruleTemplates[localIndex]! = B at hcallRoots Hsem ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, -, -, -, -, hvalid, hmotiveApp, -, -,
    hsrcLE⟩ := hsrc
  obtain ⟨origins, hshape, hstats, -, F, -⟩ := Hsem
  obtain ⟨-, -, -, -, -, callOrigins, -, hcallShape, -, -, Hcalls⟩ := hcallRoots
  have hcallOrigins : callOrigins = origins :=
    Option.some.inj (hcallShape.symm.trans hshape)
  subst callOrigins
  have hT : traversal = F.traversal := Option.some.inj (htrav.symm.trans F.traversal_eq)
  subst hT
  have hp := H.params_fvar
  have Hroot := F.rootWF.toBindingContextWF
  have hTL : BindingContextLE F.traversal.terminalContext H.localContext :=
    F.terminalExtension.contextLE
  have Hprefix : ParameterPrefix stats 0 S.constructor.type
      F.traversal.parameterTail := by
    have := F.traversal.parameterPrefix
    rwa [F.traversal_stats, F.traversal_constructor] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  have Htail := Hprefix.paramUniformIn H.params.expressions
    (I.constructorTypes owner hsourceOwner _ hctorMem).1
    (I.constructorTypes owner hsourceOwner _ hctorMem).2
  obtain ⟨hterm, hfieldsTerm⟩ := F.traversal.decisions.paramUniformIn Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ d,
      S.sourceFullContext.lctx.find? y = some d ∧
        d.DeclProjsOK (projAvoidsHeads H.localContext.env heads) := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨.cdecl index y name type bi kind, ?_, htype.2⟩
    rw [← hsrcLE.declarations y (S.fields_bound.members y hy),
      hTL.declarations y hmem, hfind]
  have hparamTerm : ∀ pv, Expr.fvar pv ∈ stats.params →
      pv ∈ F.traversal.terminalContext.lctx.fvars := fun pv h =>
    (F.traversal.decisions.freshBindings Hroot).choose_spec.1.fvars
      (F.parameterSuffix.param_mem h)
  have hfr : origins.fieldRoot = F.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins F.traversal hshape F.traversal_eq
  have hper : ∀ j, j < S.hypotheses.size →
      ∃ D : FVarDeclAt S.sourceFullContext S.hypotheses j,
        D.type.ProjsOK (projAvoidsHeads H.localContext.env heads) := by
    intro j hj
    obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, -⟩ :=
      Hcalls.rooted j hj
    rw [hstats] at hup
    rw [hfr] at hle
    have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
    have hscope : Rorigin.ParamUniformScope H.localContext.env heads stats.params.toList
        stats.levels
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) := by
      refine ⟨hup, fun fv decl hP hfind => ?_⟩
      rw [Rorigin.lctx_eq] at hfind
      rcases hP with hf | hpar
      · rw [S.fields_bound.exprArrayFVarIds] at hf
        obtain ⟨fv', index, name, type, bi, kind, hfv, hmem, hfind', htype⟩ :=
          hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hf)
        cases hfv
        rw [hle.declarations fv hmem, hfind'] at hfind
        cases hfind
        exact LocalDecl.ParamUniformIn.of_cdecl htype
      · rw [H.params.exprArrayFVarIds] at hpar
        have hmemP := H.params.mem_fvars_iff.1 hpar
        rw [hle.declarations fv (hparamTerm fv hmemP),
          ← hTL.declarations fv (hparamTerm fv hmemP)] at hfind
        exact I.paramDecls fv hpar decl hfind
    have hjr : j < S.recursiveFields.size := by rw [← S.hypotheses_size]; exact hj
    have hfieldMem : S.recursiveFields[j]! ∈ S.fields := by
      rw [← F.traversal_fields]
      apply F.traversal.decisions.selected_subset
      rw [F.traversal_recursiveFields, getElem!_pos S.recursiveFields j hjr]
      exact Array.getElem_mem hjr
    have hfieldP : ∀ fv, S.recursiveFields[j]! = .fvar fv →
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) fv := by
      intro fv hfv
      left
      rw [hfv] at hfieldMem
      exact mem_exprArrayFVarIds_of_fvar_mem hfieldMem
    have htype := O.projsOK W hp henv Rorigin hscope hfieldP
    exact ⟨D, by rw [hD]; exact htype.consumeTypeAnnotationsVerified'⟩
  rw [← S.unannotated_eq]
  refine Expr.ProjsOK.consumeTypeAnnotationsVerified' ?_
  rw [S.sourceType_eq, ← S.sourceContext_eq]
  refine Expr.ProjsOK.mkForall' S.fields_bound.expressions ?_ hfieldDecls
  refine Expr.ProjsOK.mkForall' S.hypotheses_bound.expressions ?_ ?_
  · rw [hmotiveApp]
    simp only [AddInductive.getIIndices]
    have hmo := (checkPositivityStep.isValidIndApp?_some hvalid).1
    obtain ⟨mfv, hmfv⟩ := H.motive_fvar hmo
    refine ⟨Expr.ProjsOK.mkAppN' ?_ (hterm.2.getAppArgs_slice' _),
      Expr.ProjsOK.mkAppN' (Expr.ProjsOK.mkAppN' trivial ?_) ?_⟩
    · simp only [AddInductive.getIIndices] at hmfv
      rw [hmfv]; trivial
    · intro a ha
      obtain ⟨fv, rfl⟩ := hp a ha
      trivial
    · intro a ha
      obtain ⟨y, rfl, -⟩ := FVarArrayIn.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      trivial
  · intro y hy
    obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
    have hj : j < S.hypotheses.size := by
      have := congrArg Array.size S.hypotheses_bound.expressions
      simp at this; omega
    obtain ⟨D, hDshape⟩ := hper j hj
    have hDy : D.fvar = y := by
      obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
      have := D.expression.symm.trans hget
      rw [← hjy]; exact Expr.fvar.inj this
    subst hDy
    exact ⟨_, D.declaration, hDshape⟩

section Outer

variable {heads : List Name}

/-- Index declarations (region R1): the projection component of
`indexDeclParamUniform`. -/
theorem indexDeclProjsOK (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {k : Nat} (hk : k < H.recInfos.size) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos[k]!.indices) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.DeclProjsOK (projAvoidsHeads H.localContext.env heads) := by
  obtain ⟨type, T⟩ := H.minorSources.traces k hk
  have hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      H.localContext.lctx.find? fv = some d →
        d.ParamUniformIn H.localContext.env heads stats.params.toList stats.levels := by
    intro fv hfv d hfind
    rw [H.params.exprArrayFVarIds] at hfv
    exact I.paramDecls fv hfv d hfind
  obtain ⟨-, hidx⟩ := T.paramUniform W H.params_fvar rfl hparamDecls
    (Expr.ParamUniformIn.of_avoids (I.familyHeaders k (H.sourceOwner hk)).1
      (I.familyHeaders k (H.sourceOwner hk)).2)
  have hyMem : y ∈ (H.bindings.indices k hk).fvars :=
    (H.bindings.indices k hk).mem_fvars_iff.2 hy
  obtain ⟨index, name, ty, bi, kind, hfind⟩ :=
    H.localWF.findCDecl y ((H.bindings.indices k hk).members y hyMem)
  refine ⟨_, hfind, (hidx y ?_ _ hfind).declProjsOK⟩
  rw [(H.bindings.indices k hk).exprArrayFVarIds]
  exact hyMem

/-- Major premise declarations: `I params indices`. -/
theorem majorDeclProjsOK {ok : Name → Prop} {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.DeclProjsOK ok := by
  refine H.origins.majors.declProjsOK (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.majorShapes.shape i hi']
  refine Expr.ProjsOK.consumeTypeAnnotationsVerified' ?_
  obtain ⟨n, hn⟩ := H.indConst_eq hi'
  rw [hn]
  refine Expr.ProjsOK.mkAppN' (Expr.ProjsOK.mkAppN' trivial fun a ha => ?_) fun a ha => ?_
  · obtain ⟨fv, rfl⟩ := H.params_fvar a ha
    trivial
  · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.indices i hi')
      (Array.mem_toList_iff.1 ha)
    trivial

/-- Motive declarations: `∀ indices, ∀ (t : I params indices), Sort u`. -/
theorem motiveDeclProjsOK (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.map (·.motive)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.DeclProjsOK (projAvoidsHeads H.localContext.env heads) := by
  refine H.origins.motives.declProjsOK (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.motiveShapes.shape i hi']
  refine Expr.ProjsOK.mkForall' (H.bindings.indices i hi').expressions ?_
    (fun y hy => H.indexDeclProjsOK I W hi'
      ((H.bindings.indices i hi').mem_fvars_iff.1 hy))
  refine Expr.ProjsOK.mkForall' (H.bindings.major i hi').expressions trivial
    (fun y hy => H.majorDeclProjsOK ?_)
  have h := (H.bindings.major i hi').mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hi', rfl⟩

/-- Minor premise declarations. -/
theorem minorDeclProjsOK (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.flatMap (·.minors)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.DeclProjsOK (projAvoidsHeads H.localContext.env heads) := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hy
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF i hi
  obtain ⟨Fm⟩ := H.origins.flatMinorBinderType D
  have hDy : D.fvar = y := Expr.fvar.inj (D.expression.symm.trans hget)
  subst hDy
  refine ⟨_, D.declaration, ?_⟩
  show D.type.ProjsOK (projAvoidsHeads H.localContext.env heads)
  rw [Fm.originType_eq]
  have howner := Fm.owner_lt
  have hlocal : Fm.localIndex < H.origins.minorTypes[Fm.owner]!.size := by
    rw [(H.origins.minors Fm.owner howner).size_eq, getElem!_pos H.recInfos Fm.owner howner]
    exact Fm.local_lt
  have hsrc := H.minorSources.rows Fm.owner howner (H.sourceOwner howner) Fm.localIndex hlocal
  rw [← hsrc.1]
  exact H.minorProjsOK I W Fm.owner howner Fm.localIndex hlocal

/-- **Generated recursor types satisfy the projection condition**: the
projection component of `recursorTypeParamUniform`, for the executable recursor
type `declareRecursors.recursorType` (before `inferImplicit`). -/
theorem recursorTypeProjsOK (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx
      owner).ProjsOK (projAvoidsHeads H.localContext.env heads) := by
  have hp := H.params_fvar
  have hownerC : owner < stats.indConsts.size := by
    rw [H.validStats.types_size, ← H.recInfos_size_eq]; exact howner
  obtain ⟨mfv, hmfv⟩ := H.motive_fvar hownerC
  have hmajorMem : H.recInfos[owner]!.major ∈ #[H.recInfos[owner]!.major] := by simp
  obtain ⟨jfv, hjfv, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.major owner howner) hmajorMem
  have hbody : (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major).ProjsOK (projAvoidsHeads H.localContext.env heads) := by
    refine ⟨Expr.ProjsOK.mkAppN' (by rw [hmfv]; trivial) fun a ha => ?_,
      by rw [hjfv]; trivial⟩
    obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.indices owner howner)
      (Array.mem_toList_iff.1 ha)
    trivial
  unfold AddInductive.declareRecursors.recursorType
  refine Expr.ProjsOK.mkForall' (H.params.expressions) ?_ ?_
  · refine Expr.ProjsOK.mkForall' H.bindings.motives.expressions ?_
      (fun y hy => H.motiveDeclProjsOK I W (H.bindings.motives.mem_fvars_iff.1 hy))
    refine Expr.ProjsOK.mkForall' H.bindings.flatMinors.expressions ?_
      (fun y hy => H.minorDeclProjsOK I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
    refine Expr.ProjsOK.mkForall' (H.bindings.indices owner howner).expressions ?_
      (fun y hy => H.indexDeclProjsOK I W howner
        ((H.bindings.indices owner howner).mem_fvars_iff.1 hy))
    refine Expr.ProjsOK.mkForall' (H.bindings.major owner howner).expressions hbody
      (fun y hy => H.majorDeclProjsOK ?_)
    have h := (H.bindings.major owner howner).mem_fvars_iff.1 hy
    simp only [List.mem_toArray, List.mem_singleton] at h
    rw [h]
    exact Array.mem_map.2 ⟨_, H.mem_recInfos howner, rfl⟩
  · intro y hy
    obtain ⟨index, name, type, bi, kind, hfind⟩ :=
      H.localWF.findCDecl y (H.params.members y hy)
    exact ⟨_, hfind, (I.paramDecls y hy _ hfind).declProjsOK⟩

end Outer

end RecursorConstruction

end Assembly

/-! ### The nested run -/

section Run

open Lean4Lean.InductiveSignature

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **Field `constructorProjNames`**: the lowered constructor types are
translated in the lowered header environment, which registers only the
structures of the base environment. -/
theorem NestedRun.constructorProjNames_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup) :
    ∀ lc ∈ E.lowered.loweredDecl.constructorConstants,
      lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true := by
  intro lc hlc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hlc
  obtain ⟨owner, -, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    E.lowered.constructors.core.types t ht
  obtain ⟨ctor, -, HC⟩ := Lean4Lean.List.Forall₂.forall_exists_r HT.ctors lc hc
  have hheaderV : E.lowered.headers.context.venv.Ordered :=
    E.lowered.headers.context.checking.tr.wf.ordered
  have hreg := HC.type.targetProjsRegistered hheaderV trivial VLCtx.ProjNamesOK.nil
  refine hreg.projNamesAvoid fun S ⟨info, hinfo⟩ => ?_
  rw [VEnv.addConstVals_projections_eq E.lowered.constructors.core.typesAdded,
    E.lowered_initialEnv] at hinfo
  exact E.baseProjection_not_restorable wf hadded Haux Hexpansion hnodup hinfo

/-- **Field `recursorProjNames`**: the executable recursor type satisfies the
projection condition at the heads `E.uniformHeads` (no projection out of an
auxiliary family) and is translated in the recursor-pass environment, which
registers only base structures and lowered families (no auxiliary constructor
or recursor). The generated recursor type is its translation. -/
theorem NestedRun.recursorProjNames_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup) :
    ∀ owner : Fin E.lowered.recursors.generationSignature.families.size,
      (E.lowered.recursors.canonicalGeneration.recursorType owner).projNamesAvoid
        (compilationRestoration sourceDecl auxiliaries).restorableNames = true := by
  intro owner
  have hfam := E.lowered.recursors.toRecursorConstruction.generator.familyCount
  have howner : owner.val < E.lowered.indTypes.size := by
    have := owner.isLt
    simp only [RecursorConstruction.generationSignature] at this
    omega
  have hrecSize : E.lowered.recursors.toRecursorConstruction.recInfos.size =
      E.lowered.indTypes.size := by
    rw [E.lowered.recursors.toRecursorConstruction.cardinality.records]
    simpa using (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
      E.lowered.constructors.toConstructorCheck.core).symm
  have hrec : owner.val <
      E.lowered.recursors.toRecursorConstruction.recInfos.size := by
    omega
  have htr := E.lowered.recursors.toRecursorConstruction.typeTranslations
    owner.val howner
  have hnative : (E.lowered.recursors.toRecursorConstruction.recursorTarget
      owner.val).type =
      E.lowered.recursors.canonicalGeneration.recursorType owner := by
    simp only [RecursorConstruction.recursorTarget, dif_pos owner.isLt,
      Instance.recursor]
    rfl
  rw [hnative] at htr
  have W := E.whnfPreservesParamUniform wf Hsources
  rw [← E.statsLevels] at W
  have hsrc := E.lowered.recursors.toRecursorConstruction.recursorTypeProjsOK
    (E.paramUniformDeclarations_of wf Hsources) W owner.val hrec
  have h1 := htr.projNamesOK_of_source hsrc VLCtx.ProjNamesOK.nil
  have h2 := htr.targetProjsRegistered
    E.lowered.constructors.toConstructorCheck.context.checking.tr.wf.ordered trivial
    VLCtx.ProjNamesOK.nil
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  refine (h1.and h2).projNamesAvoid fun S ⟨hhit, info, hinfo⟩ hmem => ?_
  rw [E.lowered.constructors.toConstructorCheck.contextVEnv] at hinfo
  rcases VEnv.addProjections_iff.mp hinfo with ⟨entry, hentry, rfl, -⟩ | hbase
  · simp only [VInductDecl.projectionEntries, List.mem_filterMap] at hentry
    obtain ⟨t, ht, hsome⟩ := hentry
    split at hsome
    · cases hsome
      simp only [Restoration.restorableNames, List.mem_append, hheadNames,
        compilationRestoration_recursors_fst, List.mem_map] at hmem
      rcases hmem with hmem | ⟨a, ha, hname⟩
      · exact hhit.1 (E.auxHeads_subset_uniformHeads _ hmem)
      · obtain ⟨g, hg, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
        obtain ⟨t', ht', hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hexpansion g hg
        have h1 : t.name ∈ familyNames E.lowered.loweredDecl.types :=
          List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩
        have h2 : t.name ∈ E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") := by
          refine List.mem_map.2 ⟨t', List.mem_of_mem_drop ht', ?_⟩
          rw [← hname, hev.auxiliary, ← hexp.name]
        exact (List.nodup_append.1 hnodup).2.2 _ h1 _ h2 rfl
    · cases hsome
  · rw [VEnv.addEliminators_projections,
      VEnv.addConstVals_projections_eq E.lowered.constructors.toConstructorCheck.core.ctorsAdded,
      VEnv.addConstVals_projections_eq E.lowered.constructors.toConstructorCheck.core.typesAdded,
      E.lowered_initialEnv] at hbase
    exact E.baseProjection_not_restorable wf hadded Haux Hexpansion hnodup hbase hmem

/-- **Field `equationProjNames`**: the generated equations are built from the
pieces of the generated recursor types. -/
theorem NestedRun.equationProjNames_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (Hrec : ∀ owner : Fin E.lowered.recursors.generationSignature.families.size,
      (E.lowered.recursors.canonicalGeneration.recursorType owner).projNamesAvoid
        (compilationRestoration sourceDecl auxiliaries).restorableNames = true) :
    ∀ k : Fin E.lowered.recursors.generationSignature.constructors.size,
      (E.lowered.recursors.canonicalGeneration.equation k).lhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
        (E.lowered.recursors.canonicalGeneration.equation k).rhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
        (E.lowered.recursors.canonicalGeneration.equation k).type.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true := by
  intro k
  exact Instance.equation_projNamesAvoid_of_recursorType _ _
    (Hrec E.lowered.recursors.generationSignature.constructors[k].owner) k .recursor

/-- **Fields `constructorProjNames`, `recursorProjNames` and
`equationProjNames` of `RestorationSubstitutionPremises`**, for every restoration
table of the run and every restored block base (the base and its validity
are not used): proved for the table of `restorationTablesRestoringAll`, whose
restorable names contain those of every table
(`RestorationTablesAgree.restorable_transfer`). -/
theorem NestedRun.restoredEquationProjNames_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        (∀ lc ∈ E.lowered.loweredDecl.constructorConstants,
          lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
            true) ∧
        (∀ owner : Fin E.lowered.recursors.generationSignature.families.size,
          (E.lowered.recursors.canonicalGeneration.recursorType owner).projNamesAvoid
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true) ∧
        (∀ k : Fin E.lowered.recursors.generationSignature.constructors.size,
          (E.lowered.recursors.canonicalGeneration.equation k).lhs.projNamesAvoid
              (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
            (E.lowered.recursors.canonicalGeneration.equation k).rhs.projNamesAvoid
              (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
            (E.lowered.recursors.canonicalGeneration.equation k).type.projNamesAvoid
              (compilationRestoration sourceDecl auxiliaries).restorableNames = true) := by
  intro auxiliaries D _ _ _
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, -, Haux, Hexpansion, -, D', -, -⟩
  have hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hsub : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∈ (compilationRestoration sourceDecl aux').restorableNames :=
    fun _ hn => D'.restorable_transfer D hn
  have Hrec := E.recursorProjNames_of wf Hsources hadded Haux Hexpansion hnodup
  refine ⟨fun lc hlc => VExpr.projNamesAvoid_mono hsub
      (E.constructorProjNames_of wf hadded Haux Hexpansion hnodup lc hlc),
    fun owner => VExpr.projNamesAvoid_mono hsub (Hrec owner), fun k => ?_⟩
  obtain ⟨hl, hr, ht⟩ := E.equationProjNames_of Hrec k
  exact ⟨VExpr.projNamesAvoid_mono hsub hl, VExpr.projNamesAvoid_mono hsub hr,
    VExpr.projNamesAvoid_mono hsub ht⟩

/-- **`RestorationSubstitutionPremises` from its three remaining fields**: the
eliminator-schema projection names (`eliminatorProjNames`), the typing of the
auxiliary constructor restoration lambdas (`auxiliaryConstructors`) and the
transport of the lowered projection rules (`projections`). The projection
names of the lowered constructor types, generated recursor types and
generated equations are `restoredEquationProjNames_of`. The result has the
shape of the hypothesis `G` of `restoredEquationsWF_of_substitutionPremises`. -/
theorem NestedRun.restoredEquationGaps_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Helim : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        EliminatorProjNamesAvoid (ves.venv (if isUnsafe then .unsafe else .safe))
          (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (Hcontainers : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        (∀ envTypes : VEnv,
          (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
            sourceDecl.typeConstants = some envTypes →
          ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
            ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
              h.auxiliary = lc.name →
              ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                  some restored ∧
                envTypes.HasType sourceDecl.uvars []
                  (VExpr.wrapLams E.lowered.signature.params
                    (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored) ∧
        ∀ entry ∈ E.lowered.loweredDecl.projectionEntries,
          ((compilationRestoration sourceDecl auxiliaries).interpretation
            E.lowered.signature.params).ProjectionClause B.recursorVEnv B.recursorVEnv.TypedCtx
            entry.typeName entry.info) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        RestorationSubstitutionPremises E B auxiliaries := by
  intro auxiliaries D B hB hV
  obtain ⟨hctors, hrecs, heqs⟩ := E.restoredEquationProjNames_of wf Hsources auxiliaries D B hB hV
  obtain ⟨haux, hprojs⟩ := Hcontainers auxiliaries D B hB hV
  exact
    { eliminatorProjNames := Helim auxiliaries D B hB hV
      constructorProjNames := hctors
      recursorProjNames := hrecs
      equationProjNames := heqs
      auxiliaryConstructors := haux
      projections := hprojs }

/-- **`RestorationSubstitutionPremises` from its two remaining fields**: the typing
of the auxiliary constructor restoration lambdas (`auxiliaryConstructors`) and
the transport of the lowered projection rules (`projections`). The
eliminator-schema projection names are `eliminatorProjNames_of`. -/
theorem NestedRun.restoredEquationGaps_of'
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hcontainers : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        (∀ envTypes : VEnv,
          (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
            sourceDecl.typeConstants = some envTypes →
          ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
            ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
              h.auxiliary = lc.name →
              ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                  some restored ∧
                envTypes.HasType sourceDecl.uvars []
                  (VExpr.wrapLams E.lowered.signature.params
                    (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored) ∧
        ∀ entry ∈ E.lowered.loweredDecl.projectionEntries,
          ((compilationRestoration sourceDecl auxiliaries).interpretation
            E.lowered.signature.params).ProjectionClause B.recursorVEnv B.recursorVEnv.TypedCtx
            entry.typeName entry.info) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        RestorationSubstitutionPremises E B auxiliaries := by
  exact E.restoredEquationGaps_of wf Hsources
    (fun auxiliaries D _ _ _ => E.eliminatorProjNames_of wf Hsources auxiliaries D) Hcontainers

end Run

end VerifyInductive
end Lean4Lean
