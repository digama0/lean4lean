import Lean4Lean.Verify.Inductive.Recursor.Signature.Parameters

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The executable motive telescope of a family (indices, major, elimination sort) translates
over the motive's source parameter scope to a type definitionally equal to the motive type
`S.canonical.motiveType` recorded with the motive declaration. -/
theorem MotiveDecl.unannotatedTranslation
    {Rroot : RecursorContextWF root recLparams}
    (S : MotiveDecl Rroot stats decl owner info elimLevel) :
    ∃ target,
      TrExprS Rroot.venv recLparams S.motiveSourceScope
        (root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel))) target ∧
      Rroot.venv.IsType recLparams.length S.motiveSourceScope.toCtx target ∧
      Rroot.venv.IsDefEqU recLparams.length S.motiveSourceScope.toCtx
        target S.canonical.motiveType := by
  exact ⟨S.motiveSourceTarget, S.motiveSourceTr, S.motiveSourceType,
    S.motiveSourceCanonical⟩

/-- The executable motive telescope of family `owner`, abstracted over the parameters,
translates over the recursor parameter context in the recursor-checking environment to a type
definitionally equal to the motive type recorded with its motive declaration. -/
theorem RecursorConstruction.unannotatedMotiveAtParameters
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ S : MotiveDecl H.recursorWF stats decl owner H.recInfos[owner]! H.elimLevel,
      ∃ target,
        TrExprS H.recursorWF.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
            H.params.fvars) target ∧
        H.recursorWF.venv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx target ∧
        H.recursorWF.venv.IsDefEqU
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx target S.canonical.motiveType := by
  have henv := H.recursorWF.checking.tr.wf
  obtain ⟨S, hparams⟩ := H.motiveTelescopes.motiveDecls owner howner
  rw [← H.parameterDecls] at hparams
  obtain ⟨narrowTarget, Hnarrow, HnarrowType, Hcanonical⟩ := S.unannotatedTranslation
  let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
  have HnarrowParameters : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      S.motiveParameterScope source narrowTarget := by
    simpa [source, S.motiveSourceParameterScope] using Hnarrow
  rcases cachedParameterDecls_fvars S.motiveParameterDecls with
    ⟨parameterFVars, hparameterExprs, hparameterScopeFVars⟩
  have hstatsParams : stats.params.toList.reverse =
      H.params.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList H.params.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have hparameterFVars : parameterFVars = H.params.fvars.reverse := by
    apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
    exact hparameterExprs.symm.trans hstatsParams
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
      H.params.fvars.reverse S.motiveParameterScope := by
    have Hcached := S.motiveParameterDecls
    rw [hparameterExprs, List.forall₂_map_left_iff] at Hcached
    have Hdecls' : List.Forall₂
        (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
        parameterFVars S.motiveParameterScope :=
      Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
        rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
        cases Expr.fvar.inj hparam
        exact ⟨deps, type, hentry⟩) Hcached
    simpa [hparameterFVars] using Hdecls'
  have hscopeWF := S.motiveSourceWF
  have hparamsNodup : H.params.fvars.reverse.Nodup := by
    have h := hscopeWF.fvars_nodup
    rwa [S.motiveSourceParameterScope, hparameterScopeFVars, hparameterFVars] at h
  have Habstract := Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
    (domains := []) Hdecls hparamsNodup (by
      simpa [abstractForallContext] using HnarrowParameters)
  simp only [List.reverse_reverse] at Habstract
  have Habstract' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (source.abstractList H.params.fvars) narrowTarget := by
    simpa using Habstract
  have hsourceToParams := VEnv.IsDefEqCtx.trans_empty henv
    (S.motiveParameterAlignment.symm henv.ordered) hparams
  have Hctx : VLCtx.IsDefEq H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) := by
    exact abstractForallContext.isDefEq (by simpa using hsourceToParams)
  obtain ⟨target, Htarget⟩ := Habstract'.defeqDFC henv Hctx
  have Htargets := Habstract'.uniq henv Hctx Htarget
  have Htype : H.recursorWF.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse []).toCtx narrowTarget := by
    simpa [abstractForallContext, ← S.motiveSourceParameterScope] using HnarrowType
  have Htype' := (Htype.defeqU_l henv Hctx.wf.toCtx Htargets).defeqDFC henv.ordered Hctx.defeqCtx
  have Hcanonical' : H.recursorWF.venv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse []).toCtx
      narrowTarget S.canonical.motiveType := by
    simpa [abstractForallContext, ← S.motiveSourceParameterScope] using Hcanonical
  have Hcanonical'' := (Htargets.symm.trans henv Hctx.wf.toCtx Hcanonical').defeqDFC
    henv.ordered Hctx.defeqCtx
  exact ⟨S, target, Htarget, by simpa [abstractForallContext] using Htype',
    by simpa [abstractForallContext] using Hcanonical''⟩

private theorem abstractList_sort (u : Level) (fvars : List FVarId) (k : Nat := 0) :
    (Expr.sort u).abstractList fvars k = .sort u :=
  Expr.abstractList_eq_self_of_abstract1 (.sort u)
    (by intro fv k; simp [Expr.abstract1]) fvars k

/-- The translation of `unannotatedMotiveAtParameters` has the form
`∀ indices, major → Sort level`, with one index domain per executable index and `level` the
translation of the elimination level chosen by the executable. -/
theorem RecursorConstruction.unannotatedMotiveDomains
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ S : MotiveDecl H.recursorWF stats decl owner H.recInfos[owner]! H.elimLevel,
      ∃ indices major level,
        indices.length = H.recInfos[owner]!.indices.size ∧
        VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams) H.elimLevel = some level ∧
        TrExprS H.recursorWF.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
            H.params.fvars) (VExpr.wrapForalls indices (.forallE major (.sort level))) ∧
        H.recursorWF.venv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx
          (VExpr.wrapForalls indices (.forallE major (.sort level))) ∧
        H.recursorWF.venv.IsDefEqU
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx
          (VExpr.wrapForalls indices (.forallE major (.sort level))) S.canonical.motiveType := by
  obtain ⟨S, target, Htr, Htype, Heq⟩ := H.unannotatedMotiveAtParameters owner howner
  have hlctx : LocalContext.LctxClosed H.localContext.lctx := H.recursorWF.lctxClosed
  have hparts := (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts
  have hmajorNodup : S.majorBound.fvars.Nodup := by
    rw [S.majorBound.fvars_eq (H.bindings.major owner howner) (by simp)]; exact hparts.major
  have hindicesNodup : S.indicesBound.fvars.Nodup := by
    rw [S.indicesBound.fvars_eq (H.bindings.indices owner howner) (by simp)]; exact hparts.indices
  have hmajorClosed : Closed (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel)) :=
    S.majorBound.mkForall_closed H.localWF hmajorNodup hlctx trivial
  have hinnerClosed : Closed (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))) :=
    S.indicesBound.mkForall_closed H.localWF hindicesNodup hlctx hmajorClosed
  have Hmajor := S.majorBound.mkForall_forallTelescopeList H.localWF (.sort H.elimLevel)
    hmajorNodup trivial
  have Hindices := S.indicesBound.mkForall_forallTelescopeList H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    hindicesNodup hmajorClosed
  have Htel := (Hindices.trans (Hmajor.abstractList S.indicesBound.fvars)).abstractList H.params.fvars
  simp only [Array.size_singleton, abstractList_sort, Nat.zero_add] at Htel
  obtain ⟨domains, result, hlength, htarget, Hresult⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Htr
  cases Hresult with
  | sort hlevel =>
    rename_i level
    have hnonempty : domains ≠ [] := by intro heq; simp [heq] at hlength
    let indices := domains.dropLast
    let major := domains.getLast hnonempty
    have hdomains : indices ++ [major] = domains := List.dropLast_concat_getLast hnonempty
    have hindices : indices.length = H.recInfos[owner]!.indices.size := by
      rw [← hdomains, List.length_append, List.length_singleton] at hlength
      omega
    have htarget' : target = VExpr.wrapForalls indices (.forallE major (.sort level)) := by
      rw [htarget, ← hdomains, VExpr.wrapForalls_append]
      rfl
    rw [htarget'] at Htr Htype Heq
    exact ⟨S, indices, major, _, hindices, hlevel, Htr, Htype, Heq⟩

/-- Every constant of an atomic batch is non-delta. -/
theorem AtomicAddConstants.entries_delta
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv) :
    ∀ e ∈ entries, e.1.deltaValue? = none := by
  induction H with
  | nil => simp
  | cons _ _ _ _ hdelta _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hdelta
    · exact ih e he

/-- An atomic batch of non-delta constants adds no definition. -/
theorem AtomicAddConstants.defnReflect
    (H : AtomicAddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) {n : Name} {v : DefinitionVal}
    (hfind : outEnv.find? n = some (.defnInfo v)) : env.find? n = some (.defnInfo v) := by
  rcases H.entryOrigin hwf hfind with h | ⟨entry, hentry, -, heq⟩
  · exact h
  · have := H.entries_delta entry hentry
    rw [← heq] at this
    cases this

/-- A batch of non-delta constants adds no definition. -/
theorem AddConstants.defnReflect
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) {n : Name} {v : DefinitionVal}
    (hfind : outEnv.find? n = some (.defnInfo v)) : env.find? n = some (.defnInfo v) :=
  (AtomicAddConstants.ofAddConstants H).defnReflect hwf hfind

/-- A family of the block is not accepted as a type-annotation wrapper by the
constructor environment: a wrapper is a definition, the constructor environment
adds no definition to the source environment, and the families are fresh there. -/
theorem ConstructorCheck.family_not_wrapper
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    ctorEnv.isTypeAnnotationWrapper family.name = false := by
  have hfresh := (VEnv.addConstVals_names_fresh R.core.typesAdded).2
    family.toVConstVal (List.mem_map.mpr ⟨family, hf, rfl⟩)
  cases hw : ctorEnv.isTypeAnnotationWrapper family.name with
  | false => rfl
  | true =>
    exfalso
    unfold Kernel.Environment.isTypeAnnotationWrapper at hw
    split at hw
    · rename_i v hfindCtor
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      have hsafe : v.safety = .safe := hw.1.1
      have Hsource := R.sourceContext.checking
      have hsourceWF := Hsource.tr.map_wf
      rw [R.sourceContextVEnv] at Hsource
      have hfindSource : c.env.find? family.name = some (.defnInfo v) := by
        cases R.installation with
        | ordinary Htypes Hctors =>
          have Hheader := (Htypes.validCore Hsource.toValidCore).tr
          exact Htypes.defnReflect hsourceWF (Hctors.defnReflect Hheader.map_wf hfindCtor)
        | primitive Htypes Hctors _ _ =>
          have Hheader := Htypes.checking Hsource.tr
          exact Htypes.defnReflect hsourceWF (Hctors.defnReflect Hheader.map_wf hfindCtor)
      obtain ⟨value, hvalue, _⟩ := R.sourceContext.checking.tr.find? hfindSource
        (by simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hsafe,
          DefinitionSafety.le_safe])
      rw [R.sourceContextVEnv, hfresh] at hvalue
      cases hvalue
    · simp at hw

theorem Expr.consumeTypeAnnotationsVerified_eq_of_head {ok : Name → Bool} {e : Expr}
    (hhead : e.getAppFn = .const name levels) (hok : ok name = false) :
    (e.consumeTypeAnnotationsVerified ok) = e := by
  fun_induction Expr.consumeTypeAnnotationsVerified ok e
  case case1 n ls first second hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hok] at hannotation
  case case3 n ls arg hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hok] at hannotation
  all_goals rfl

/-- The type of the major premise is the source family applied to the parameters and indices:
removing type annotations leaves it unchanged, since no family of the block is a
type-annotation wrapper. -/
theorem RecursorConstruction.majorSourceType
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (D : FVarDeclAt H.localContext #[H.recInfos[owner]!.major] 0) :
    D.type = mkAppN (mkAppN
      (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        stats.levels) stats.params) H.recInfos[owner]!.indices := by
  have hfamily : owner < decl.types.length := by simpa [H.cardinality.records] using howner
  let Dall : FVarDeclAt H.localContext (H.recInfos.map (·.major)) owner := {
    D with
    inBounds := by simpa using howner
    expression := by
      simpa [Array.getElem!_eq_getD, Array.getD, howner] using D.expression }
  have htype := (H.origins.majors.type_eq Dall).trans (H.majorShapes.shape owner howner)
  have hconst : stats.indConsts[owner]! = .const decl.types[owner].name stats.levels := by
    rw [R.statsWF.consts]
    simp [hfamily]
  rw [hconst] at htype
  change D.type = _ at htype
  rw [htype, H.localExtends.env_eq]
  apply Expr.consumeTypeAnnotationsVerified_eq_of_head
    (name := decl.types[owner].name) (levels := stats.levels)
  · simp [Expr.getAppFn_mkAppN, Expr.getAppFn]
  · exact R.family_not_wrapper _ (List.getElem_mem hfamily)

/-- The domain of binder `i` of a telescope translating to `wrapForalls domains result`
translates to `domains[i]` over the context extended by the first `i` domains. -/
theorem Expr.ForallBinderAt.translation
    (Hb : Expr.ForallBinderAt source i domain)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (hi : i < domains.length) :
    TrExprS env Us (abstractForallContext (domains.take i) Δ) domain domains[i] := by
  induction Hb generalizing Δ domains result with
  | here =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ Hdom _ => simpa [abstractForallContext] using Hdom
  | @there body i domain name outerDomain bi Hb ih =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ _ Hbody =>
        have ht := ih Hbody (by simpa using hi)
        simpa [abstractForallContext, List.map_append, List.append_assoc] using ht

theorem Expr.abstractList_fullApp
    (fvars : List FVarId) (hnd : fvars.Nodup) (name : Name) (levels : List Level) :
    (mkAppN (.const name levels) (fvars.map Expr.fvar).toArray).abstractList fvars =
      Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin fvars.length => Expr.bvar (fvars.length - 1 - i)) := by
  rw [Expr.abstractList_mkAppN, Expr.abstractList_const,
    Expr.abstractList_fvarArray fvars 0 hnd, Expr.mkAppN_eq_mkAppList]
  simp

theorem RecursorConstruction.majorBinderSource
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    Expr.ForallBinderAt
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      H.recInfos[owner]!.indices.size
      (Expr.mkAppList
        (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name stats.levels)
        (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
          Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i))) := by
  have hfamily : owner < decl.types.length := by simpa [H.cardinality.records] using howner
  let I := H.bindings.indices owner howner
  let M := H.bindings.major owner howner
  have hparts := (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts
  have hparams : H.params.fvars.Nodup := hparts.params
  have hindices : I.fvars.Nodup := hparts.indices
  have hmajor : M.fvars.Nodup := hparts.major
  have hcombined : (H.params.fvars ++ I.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hparams, hindices, ?_⟩
    intro a ha b hb
    exact hparts.params_later a ha b (by simp [RecInfoBindings.toRecursorBinderGroups,
      FVarArrayIn.toCDeclArray, I, hb])
  have hsizeI : I.fvars.length = H.recInfos[owner]!.indices.size := by
    simpa using congrArg Array.size I.expressions.symm
  have hsizeP : H.params.fvars.length = stats.params.size := by
    simpa using congrArg Array.size H.params.expressions.symm
  obtain ⟨D⟩ := M.declarationAt H.localWF 0 (by simp)
  have hlctx : LocalContext.LctxClosed H.localContext.lctx := H.recursorWF.lctxClosed
  have hDtype : Closed D.type := hlctx.cdecl D.declaration
  have Hb := (M.toCDeclArray H.localWF).forallBinderAtList hmajor D hDtype
    (body := .sort H.elimLevel)
  simp only [List.take_zero, Expr.abstractList] at Hb
  have hmajorClosed : Closed (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel)) :=
    M.mkForall_closed H.localWF hmajor hlctx trivial
  have HI := I.mkForall_forallTelescopeList H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    hindices hmajorClosed
  have Hclosed := (HI.prependBinderAt (Hb.abstractList I.fvars)).abstractList H.params.fvars
  simp only [Nat.add_zero, Nat.zero_add] at Hclosed
  have hdomain := Expr.abstractList_after_inner (e := D.type)
    (outer := H.params.fvars) (inner := I.fvars) (k := 0) hcombined
  simp only [Nat.zero_add, hsizeI] at hdomain
  rw [hdomain] at Hclosed
  rw [H.majorSourceType owner howner D] at Hclosed
  have hsource : mkAppN
      (mkAppN (.const decl.types[owner].name stats.levels) stats.params)
        H.recInfos[owner]!.indices =
      mkAppN (.const decl.types[owner].name stats.levels)
        ((H.params.fvars ++ I.fvars).map Expr.fvar).toArray := by
    conv => lhs; rw [H.params.expressions, I.expressions]
    simp [Expr.mkAppN_eq_mkAppList, List.map_append, Expr.mkAppList_append]
  rw [hsource, Expr.abstractList_fullApp _ hcombined] at Hclosed
  have hvars :
      (List.ofFn fun i : Fin (H.params.fvars ++ I.fvars).length =>
        Expr.bvar ((H.params.fvars ++ I.fvars).length - 1 - i)) =
      (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
        Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i)) := by
    apply List.ext_getElem
    · simp [hsizeP, hsizeI]
    · intro i hi hj
      simp [hsizeP, hsizeI]
  rwa [hvars] at Hclosed

theorem TrExprS.const_bvarSpine_eq
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some vlevels)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i))) target)
    (hn : n ≤ domains.length) :
    target = VExpr.mkApps (.const name vlevels) (bvarSpine n) := by
  let args := List.ofFn fun i : Fin n => n - 1 - i
  have hargs : ∀ i ∈ args, i < domains.length := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    have := j.isLt
    omega
  have hsource : Expr.mkAppList (.const name levels)
      (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.foldl (fun fn i => .app fn (.bvar i)) (.const name levels) := by
    rw [show (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.map Expr.bvar by simp [args, List.map_ofFn, Function.comp_def]]
    simp [Expr.mkAppList_eq_foldl, List.foldl_map]
  rw [hsource] at Htr
  have heq := TrExprS.foldl_bvars_eq domains Δ args hargs (.const name levels)
    (.const name vlevels) (fun out Hconst => by
      cases Hconst with
      | const _ hlevels _ =>
        rw [Hlevels] at hlevels
        cases Option.some.inj hlevels
        rfl) Htr
  have htargets : bvarSpine n = args.map VExpr.bvar := by
    simp [bvarSpine_eq_ofFn, args, List.map_ofFn, Function.comp_def]
  simpa [VExpr.mkApps, htargets, List.foldl_map] using heq

/-- In every translation of the executable motive telescope, the major's domain is the family
applied to the bvar spine of parameters and indices; the index domains are determined only up
to definitional equality. -/
theorem RecursorConstruction.unannotatedMotiveMajor
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (hindices : indices.length = H.recInfos[owner]!.indices.size)
    (hlevels : stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)) = some levels)
    (Htr : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      (VExpr.wrapForalls indices (.forallE major result))) :
    major = VExpr.mkApps
      (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name levels)
      (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size)) := by
  have Hclosed := H.majorBinderSource owner howner
  have Htr' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      (VExpr.wrapForalls (indices ++ [major]) result) := by
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls] using Htr
  have Hdomain := Hclosed.translation Htr' (by simp [hindices])
  have htake : (indices ++ [major]).take H.recInfos[owner]!.indices.size = indices := by
    rw [← hindices]
    simp
  have hget : (indices ++ [major])[H.recInfos[owner]!.indices.size]'(by simp [hindices]) = major := by
    simp [← hindices]
  rw [htake, hget] at Hdomain
  have Hdomain' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ indices) [])
      (Expr.mkAppList (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        stats.levels)
        (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
          Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i))) major := by
    simpa [abstractForallContext, List.map_append, List.append_assoc] using Hdomain
  apply TrExprS.const_bvarSpine_eq hlevels Hdomain'
  have hlength := Lean4Lean.List.Forall₂.length_eq H.parameterSuffix.cached
  have hctxLength := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
    H.parameterSuffix.cached
  simp only [List.length_append, List.length_reverse, hctxLength, hindices]
  simpa using Nat.le_of_eq (congrArg (· + H.recInfos[owner]!.indices.size)
    (by simpa using hlength))

end Lean4Lean.VerifyInductive
