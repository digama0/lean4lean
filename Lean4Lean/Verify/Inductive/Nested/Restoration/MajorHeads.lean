import Lean4Lean.Verify.Inductive.Nested.Restoration.Recursors

/-! The restored major heads of a nested run's recursors (`NestedRun.restoredMajorHead`,
`NestedRun.auxNestedHead`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open InductiveSignature
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! ### Forall binders under instantiation and replacement -/

theorem Expr.ForallBinderAt.instantiate1'
    (H : Expr.ForallBinderAt source i domain) (a : Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiate1' a k) i
      (domain.instantiate1' a (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.instantiate1'] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.instantiate1' a (k + 1))
          (bi := bi) (domain := domain.instantiate1' a k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.instantiate1' a k)
        (bi := bi) Htail
      simpa [Expr.instantiate1', Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.instantiateRevList
    (H : Expr.ForallBinderAt source i domain) (as : List Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiateRevList as k) i
      (domain.instantiateRevList as (k + i)) := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simpa only [Expr.instantiateRevList] using ih.instantiate1' a k

theorem Expr.getAppFn_instantiateRevList_of_const {e : Expr} {as : List Expr}
    {k : Nat} {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiateRevList as k).getAppFn = .const n ls := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simp only [Expr.instantiateRevList]
      exact Expr.getAppFn_instantiate1'_of_const ih

/-- A forall prefix followed by a binder selects that binder of the
residual. -/
theorem Expr.ForallTelescope.dropBinderAt
    (Hprefix : Expr.ForallTelescope outer n middle)
    (Hbinder : Expr.ForallBinderAt outer (n + i) domain) :
    Expr.ForallBinderAt middle i domain := by
  induction Hprefix with
  | nil => simpa using Hbinder
  | @cons body arity result name dom bi Hprefix ih =>
      have : arity + 1 + i = (arity + i) + 1 := by omega
      rw [this] at Hbinder
      cases Hbinder with
      | there H => exact ih H

/-- A replacement which never fires at a forall node keeps every forall
binder, replacing its domain. -/
theorem ExprReplacement.binderAt
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Hbinder : Expr.ForallBinderAt input i domain) :
    ∃ domain', Expr.ForallBinderAt output i domain' ∧
      ExprReplacement replaceNode domain domain' := by
  induction Hbinder generalizing output with
  | @here name dom body bi =>
      cases Hreplace with
      | occurrence h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          refine ⟨_, ?_, hdom⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.here (name := name) (body := _) (bi := bi)
              (domain := _))
  | @there body i domain name outerDomain bi H ih =>
      cases Hreplace with
      | occurrence h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          rcases ih hbody with ⟨domain', Hd, Hr⟩
          refine ⟨domain', ?_, Hr⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.there (name := name) (outerDomain := _)
              (bi := bi) Hd)

/-- The application head of a replaced expression: a constant head `c`
satisfying `Good` stays a constant head satisfying `Good`, provided every
replacement on the spine produces such a head. -/
theorem ExprReplacement.constHead {Good : Name → Prop}
    (Hhit : ∀ t out, (∃ ls, t.getAppFn = .const c ls) →
      replaceNode t = some out → ∃ c' ls', out.getAppFn = .const c' ls' ∧ Good c')
    (hc : Good c)
    (Hreplace : ExprReplacement replaceNode input output)
    (hhead : input.getAppFn = .const c ls) :
    ∃ c' ls', output.getAppFn = .const c' ls' ∧ Good c' := by
  induction Hreplace with
  | occurrence h => exact Hhit _ _ ⟨ls, hhead⟩ h
  | @const name levels h =>
      exact ⟨name, levels, rfl, by
        simp only [Expr.getAppFn, Expr.const.injEq] at hhead
        rw [hhead.1]; exact hc⟩
  | @app fn arg fn' arg' h hfn harg ihfn _ =>
      have hfnHead : fn.getAppFn = .const c ls := by
        simpa [Expr.getAppFn] using hhead
      rcases ihfn hfnHead with ⟨c', ls', hout, hgood⟩
      exact ⟨c', ls', by simpa [Expr.updateApp!, Expr.getAppFn] using hout, hgood⟩
  | bvar | fvar | mvar | sort | lit | lam | forallE | letE | mdata | proj =>
      simp [Expr.getAppFn] at hhead

/-- A translated concrete expression with a constant application head
translates to an application spine of the same constant. -/
theorem TrExprS.constHead_eq {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfn : e.getAppFn = .const c ls)
    (he' : e' = VExpr.mkApps (.const n us) args) : c = n := by
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at H
  rcases checkPositivityStep.TrExprS.mkAppList_inv H with ⟨fn', args', hfn', -, rfl⟩
  cases hfn' with
  | const _ _ _ =>
    have h := congrArg VExpr.getAppFnArgs he'
    rw [VExpr.getAppFnArgs_mkApps_const, VExpr.getAppFnArgs_mkApps_const] at h
    simp only [Prod.mk.injEq, VExpr.const.injEq] at h
    exact h.1.1

/-! ### The major binder of a generated recursor -/

/-- The domain at the major position of a generated recursor type is an
application of the owner family constant. -/
theorem RecursorInstallation.generated_majorBinder
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    ∃ domain, Expr.ForallBinderAt (H.generated.entry owner howner).info.type
        (H.generated.entry owner howner).info.getMajorIdx domain ∧
      domain.getAppFn = .const (decl.types[owner]'(by
        rw [← H.cardinality.records, ← H.generated.length]; exact howner)).name
        stats.levels := by
  have hrecInfo : owner < H.recInfos.size := by
    rw [← H.generated.length]; exact howner
  let E := H.generated.entry owner howner
  let S := H.bindings.toRecursorBinderGroups H.localWF H.params owner hrecInfo
  have hnoalias : S.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  obtain ⟨D⟩ := (H.bindings.major owner hrecInfo).declarationAt H.localWF 0 (by simp)
  have Hbinder := S.majorBinderAt hnoalias D
  dsimp only at Hbinder
  rw [← E.type] at Hbinder
  have hidx : E.info.getMajorIdx = stats.params.size + (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size := by
    simp only [Lean.RecursorVal.getMajorIdx, E.numParams, E.numMotives, E.numMinors,
      E.numIndices, H.arities owner hrecInfo]
  rw [← hidx] at Hbinder
  refine ⟨_, Hbinder, ?_⟩
  apply Expr.getAppFn_abstractN_const
  rw [H.majorSourceType owner hrecInfo D]
  simp [Expr.getAppFn_mkAppN, Expr.getAppFn]

theorem _root_.Lean.Expr.ParamUniform.binderAt {heads : List Name} {params : List Expr}
    {ls : List Level} {e : Expr} (H : e.ParamUniform heads params ls)
    (Hbinder : Expr.ForallBinderAt e i domain) : domain.ParamUniform heads params ls := by
  induction Hbinder with
  | here => exact H.forallE_inv.1
  | there _ ih => exact ih H.forallE_inv.2

/-! ### The major inductive of a restored recursor -/

section MajorHead

variable {result : Lean4Lean.ElimNestedInductive.Result}
  {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
  {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
  {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
  {outEnv : Environment}

/-- The domain at the major position of a restored recursor's concrete type
is an application of a constant: the owner family itself when it is not a
restoration head, and otherwise the head of the nested occurrence recorded
for the owner family by lowering. -/
theorem NestedRun.restoredMajorHead {ves : VEnvs}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {r : Restoration} {auxRec : NameMap Name} {targetEnv : VEnv} {Us : List Name}
    {auxLevels : List Level}
    (A : RestorationMapAgreement r result E.loweredEnv auxRec targetEnv Us auxLevels)
    (hheads : r.heads.map (·.auxiliary) = E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (hparamsFVars : ∃ xs : List FVarId, result.params = ⟨xs.map .fvar⟩)
    (hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {allIndNames : List Name} {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget)
    (hfamRec : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst)
    (hfamKey : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find? (E.lowered.loweredDecl.types[owner.val]'hi).name =
        some nested) :
    ∃ (hi : owner.val < E.lowered.loweredDecl.types.length) (domain : Expr) (c : Name)
      (ls : List Level),
      Expr.ForallBinderAt Hstep.restored.newInfo.type Hstep.restored.newInfo.getMajorIdx
        domain ∧
      domain.getAppFn = .const c ls ∧
      (((E.lowered.loweredDecl.types[owner.val]'hi).name ∉ r.heads.map (·.auxiliary) ∧
          c = (E.lowered.loweredDecl.types[owner.val]'hi).name) ∨
        ∃ nested ls', result.aux2nested.find?
            (E.lowered.loweredDecl.types[owner.val]'hi).name = some nested ∧
          nested.getAppFn = .const c ls') := by
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  obtain ⟨Dfull, Hfull, hDfull⟩ :=
    E.lowered.recursors.generated_majorBinder owner.val hi
  have hnp := (E.lowered.recursors.generated.entry owner.val hi).numParams
  rw [hinfo] at Hfull hnp
  have hdecl : owner.val < E.lowered.loweredDecl.types.length := by
    have h := E.lowered.recursors.generated.length
    rw [E.lowered.recursors.cardinality.records] at h
    rw [← h]; exact hi
  refine ⟨hdecl, ?_⟩
  have hfamRec' := hfamRec hdecl
  have hfamKey' := hfamKey hdecl
  clear hfamRec hfamKey
  generalize (E.lowered.loweredDecl.types[owner.val]'hdecl).name = fam
    at hDfull hfamRec' hfamKey' ⊢
  have R := Hstep.restored.restoration
  have hidx : Hstep.restored.newInfo.getMajorIdx = Hstep.oldInfo.getMajorIdx := by
    simp only [Lean.RecursorVal.getMajorIdx, R.numParams, R.numMotives, R.numMinors,
      R.numIndices]
  rw [E.statsParamsSize] at hnp
  obtain ⟨k, hk⟩ : ∃ k, Hstep.oldInfo.getMajorIdx = result.nparams + k :=
    ⟨Hstep.oldInfo.getMajorIdx - result.nparams, by
      simp only [Lean.RecursorVal.getMajorIdx] at *; omega⟩
  rw [hk] at Hfull
  rw [hidx, hk]
  obtain ⟨suffix, Htel⟩ := E.loweredRecursorParameterTelescope owner Hstep
  have Hsuffix := Htel.dropBinderAt Hfull
  obtain ⟨Hopen⟩ := R.type.opening hparamsSize
  obtain ⟨fvars, _hAs, _hlen, hbody⟩ := Hopen.opening.forallResidualData Htel
  have Hbody : Expr.ForallBinderAt Hopen.body k
      (Dfull.instantiateRevList (fvars.map Expr.fvar) k) := by
    rw [hbody]
    simpa using Hsuffix.instantiateRevList (fvars.map Expr.fvar) 0
  have hold : (Dfull.instantiateRevList (fvars.map Expr.fvar) k).getAppFn =
      .const fam E.lowered.stats.levels :=
    Expr.getAppFn_instantiateRevList_of_const hDfull
  obtain ⟨newDom, HnewB, Hrep⟩ := ExprReplacement.binderAt
    (fun _ _ _ _ => restoreNestedNode_forall result E.loweredEnv Hopen.params auxRec)
    Hopen.replacement Hbody
  have HnewFull := (Hopen.outputPrefixTelescope Htel).prependBinderAt
    (HnewB.abstractN Hopen.selection.fvars 0)
  simp only [Nat.zero_add] at HnewFull
  suffices Hhead : ∃ c ls, newDom.getAppFn = .const c ls ∧
      ((fam ∉ r.heads.map (·.auxiliary) ∧ c = fam) ∨
        ∃ nested ls', result.aux2nested.find? fam = some nested ∧
          nested.getAppFn = .const c ls') by
    obtain ⟨c, ls, hc, hgood⟩ := Hhead
    exact ⟨_, c, ls, HnewFull, Expr.getAppFn_abstractN_const hc, hgood⟩
  by_cases hmem : fam ∈ r.heads.map (·.auxiliary)
  · obtain ⟨nested, hnested⟩ := hfamKey' hmem
    obtain ⟨I0, lsI, hnestedFn⟩ := hnestedHead fam nested hnested
    have Hshape := (E.recursorParamUniform_of_wfCore wf Hsources owner Hstep).1
    rw [← hheads] at Hshape
    obtain ⟨HbodyShape, hsize, -⟩ := Hopen.paramUniform_of_lowered Htel Hshape
    have HdomShape := HbodyShape.binderAt Hbody
    obtain ⟨-, rest, hargs, -⟩ := HdomShape.getAppFn_const_head_inv hold hmem
    have hH : restoreHead result E.loweredEnv Hopen.params fam =
        some ((nested.abstract result.params).instantiateRev Hopen.params) := by
      simp [restoreHead, hnested]
    have hnotrec : ∀ c ls, Dfull.instantiateRevList (fvars.map Expr.fvar) k = .const c ls →
        auxRec.find? c = none := by
      intro c ls h
      have hc : c = fam := by
        rw [h] at hold; simp only [Expr.getAppFn, Expr.const.injEq] at hold; exact hold.1
      subst hc
      exact A.notRecursor_of_head (by rw [hH]; simp)
    have hnode := restoreNestedNode_eq_of_restoreHead result E.loweredEnv Hopen.params auxRec
      _ hnotrec hold hH (by rw [hargs]; simp; omega)
    have hout := Hrep.output_of_occurrence hnode
    refine ⟨I0, lsI, ?_, Or.inr ⟨nested, lsI, hnested, hnestedFn⟩⟩
    rw [hout, Expr.getAppFn_mkAppList]
    obtain ⟨xs, hxs⟩ := hparamsFVars
    rw [hxs, Expr.abstractN_eq, Expr.instantiateRev_eq, Expr.instantiate_eq]
    exact Expr.getAppFn_instantiateList_of_const (Expr.getAppFn_abstractN_const hnestedFn)
  · have hrecName : ∀ new, auxRec.find? fam = some new → new = fam := by
      intro new hnew
      have h1 := A.recursorName fam
      rw [Restoration.recursorName_of_not_mem hfamRec', hnew] at h1
      exact h1.symm
    have hnoneHead : restoreHead result E.loweredEnv Hopen.params fam = none :=
      A.restoreHead_eq_none hmem
    have Hhit : ∀ t out, (∃ ls, t.getAppFn = .const fam ls) →
        result.restoreNestedNode E.loweredEnv Hopen.params auxRec t = some out →
        ∃ c' ls', out.getAppFn = .const c' ls' ∧ c' = fam := by
      rintro t out ⟨ls0, hfn⟩ hsome
      by_cases ht : ∃ ls1, t = .const fam ls1
      · obtain ⟨ls1, rfl⟩ := ht
        cases hrec : auxRec.find? fam with
        | none =>
          rw [restoreNestedNode_eq_none_of_restoreHead result E.loweredEnv Hopen.params auxRec _
            (fun c ls h => by cases h; exact hrec)
            (fun c ls h => by
              simp only [Expr.getAppFn, Expr.const.injEq] at h
              rw [← h.1]; exact hnoneHead)] at hsome
          cases hsome
        | some new =>
          rw [restoreNestedNode_recursor result E.loweredEnv Hopen.params auxRec fam new ls1
            hrec] at hsome
          cases hsome
          exact ⟨new, ls1, rfl, hrecName new hrec⟩
      · rw [restoreNestedNode_eq_none_of_restoreHead result E.loweredEnv Hopen.params auxRec t
          (fun c ls h => by
            exfalso; apply ht
            subst h
            simp only [Expr.getAppFn, Expr.const.injEq] at hfn
            exact ⟨ls, by rw [hfn.1]⟩)
          (fun c ls h => by
            rw [hfn] at h; cases h; exact hnoneHead)] at hsome
        cases hsome
    obtain ⟨c', ls', hc', hgood⟩ := ExprReplacement.constHead (Good := (· = fam)) Hhit rfl
      Hrep hold
    exact ⟨c', ls', hc', Or.inl ⟨hmem, hgood⟩⟩

/-- Every nested occurrence recorded by lowering is headed by an inductive
type of the source kernel environment. -/
theorem NestedRun.auxNestedHead {ves : VEnvs}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {name : Name} {nested : Expr} (hfind : result.aux2nested.find? name = some nested) :
    ∃ I ls info, nested.getAppFn = .const I ls ∧
      sourceProdEnv.find? I = some (.inductInfo info) := by
  rcases E.lowering with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  rcases Hrun.cachedAuxiliaryFamilyOfLookup
      (VEnvs.WF.environmentTypesClosed wf) wf.inductivesClosed Hsources rfl rfl hfind with
    ⟨O⟩
  have hhead := O.origin.generated.built.nested_getAppFn O.origin.generated.selection
    O.origin.generated.argsArity
  rw [O.nested_eq] at hhead
  exact ⟨_, _, _, hhead, O.origin.generated.built.lookup⟩


/-- The source family names are the names of the source prefix of the
lowered declaration. -/
theorem NestedRun.sourceNames_eq
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L) :
    sourceTypes.map (·.name) =
      (E.lowered.loweredDecl.types.take sourceTypes.length).map (·.name) :=
  forall₂_map_eq (fun _ _ h => h.name.symm) E.sourceCore.sourceHeaders

end MajorHead

end VerifyInductive
end Lean4Lean
