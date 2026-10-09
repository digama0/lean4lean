import Lean4Lean.Verify.Inductive.Recursor.Signature.MotiveDomains
import Lean4Lean.Verify.Inductive.Recursor.Context.DeclarationUniverses
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The first `n` forall binders of an expression, closed with `Prop` in place of the residual.
Applied to a motive type it drops the major and the elimination sort, so that the index
domains can be read in the source universes. -/
def Expr.forallDomainsOnly : Nat → Expr → Expr
  | 0, _ => .sort .zero
  | n + 1, .forallE name domain body bi =>
      .forallE name domain (forallDomainsOnly n body) bi
  | _, _ => .sort .zero

theorem Expr.ForallTelescope.domainsOnly
    (H : Expr.ForallTelescope source n residual) :
    Expr.ForallTelescope (Expr.forallDomainsOnly n source) n (.sort .zero) := by
  induction H with
  | nil => exact .nil _
  | cons H ih => exact .cons ih

/-- A translation of a telescope to `wrapForalls domains result` restricts to a translation of
its first `n` domains (`Expr.forallDomainsOnly`) to `wrapForalls domains Prop`, which is a type. -/
theorem TrExprS.forallDomainsOnly
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result)) :
    TrExprS env Us Δ (Expr.forallDomainsOnly n source)
        (VExpr.wrapForalls domains (.sort .zero)) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains (.sort .zero)) := by
  induction Htel generalizing domains Δ result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    exact ⟨.sort rfl, ⟨_, .sort trivial⟩⟩
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons domain domains =>
      cases Htr with
      | forallE HdomType _ Hdom Hbody =>
        obtain ⟨Hbody', HbodyType⟩ := ih (by simpa using hlen) Hbody
        exact ⟨.forallE HdomType HbodyType Hdom Hbody', .forallE HdomType HbodyType⟩

/-- If a telescope translates at the universe parameters `fresh :: Us` and its first `n`
domains do not mention `fresh`, then those domains also translate at `Us` to some
`sourceDomains`, which form a type, and shifting `sourceDomains` past `fresh` gives a
translation at `fresh :: Us`. The domains of the given translation need not be syntactically
these shifts. -/
theorem TrExprS.chooseDeclUnivForallDomains
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hfresh : fresh ∉ Us)
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htr : TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length))
      source (VExpr.wrapForalls domains result))
    (hsource : Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh)
      (Expr.forallDomainsOnly n source) = Expr.forallDomainsOnly n source) :
    ∃ sourceDomains,
      sourceDomains.length = n ∧
      TrExprS env Us Δ (Expr.forallDomainsOnly n source)
        (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length))
        (Expr.forallDomainsOnly n source)
        (VExpr.wrapForalls (sourceDomains.map (VExpr.instL (VLevel.prependShift Us.length)))
          (.sort .zero)) := by
  obtain ⟨Hprefix, HprefixType⟩ := TrExprS.forallDomainsOnly Htel hlen Htr
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  have hctx := (show VLCtx.WF env (VLevel.prependShift Us.length).length Δ from by
    simpa using hΔ).instL hshift
  have Hsource := Hprefix.dropFreshLevelParam (by simpa using hctx)
  rw [hsource, hΔ.prepend_drop_levels, VExpr.instL_wrapForalls] at Hsource
  let sourceDomains := domains.map (VExpr.instL (recursorDropLevels Us.length))
  have Hsource' : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls sourceDomains (.sort .zero)) := Hsource
  have Htype := HprefixType.instL (recursorDropLevels_wf (n := Us.length))
  have hcontext := congrArg VLCtx.toCtx hΔ.prepend_drop_levels
  rw [VLCtx.instL_toCtx] at hcontext
  rw [hcontext, VExpr.instL_wrapForalls] at Htype
  refine ⟨sourceDomains, by simp [sourceDomains, hlen], Hsource', Htype, ?_⟩
  simpa [VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst] using
    Hsource'.prependLevelParam henv hΔ hfresh

theorem ConstructorCheck.sourceAnonymousParameterWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VLCtx.WF R.context.venv c.lparams.length
      (abstractForallContext R.parameterScope.toCtx.reverse []) := by
  have Hparams := R.recursorHeaders.paramsContext
  rw [R.recursorHeaders_parameterScope] at Hparams
  have Hctx := abstractForallContext.isDefEq
    (right := R.parameterScope.toCtx.reverse) (by simpa using Hparams)
  exact (Hctx.symm R.context.checking.tr.wf.ordered).wf

theorem RecursorConstruction.parameterAnonymousContext
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) :
    abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [] =
      (abstractForallContext R.parameterScope.toCtx.reverse []).instL
        (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) := by
  rw [VLCtx.instL_abstractForallContext, H.parameterDomains]
  rfl

/-- The executable index telescope of family `owner`: its motive type, abstracted over the
parameters, with the major binder and elimination sort removed (`Expr.forallDomainsOnly`). -/
def RecursorConstruction.indexDomainSource
    (H : RecursorConstruction R) (owner : Nat) : Expr :=
  Expr.forallDomainsOnly H.recInfos[owner]!.indices.size
    ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
        H.params.fvars)

theorem Expr.forallDomainsOnly_abstract1 (n : Nat) (source : Expr) (fv : FVarId) (k : Nat) :
    Expr.forallDomainsOnly n (source.abstract1 fv k) =
      (Expr.forallDomainsOnly n source).abstract1 fv k := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    cases source <;> simp [Expr.forallDomainsOnly, Expr.abstract1, ih]
    all_goals split <;> rfl

theorem Expr.forallDomainsOnly_abstractList (n : Nat) (source : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.forallDomainsOnly n (source.abstractList fvars k) =
      (Expr.forallDomainsOnly n source).abstractList fvars k := by
  induction fvars generalizing source k with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList, ih, Expr.forallDomainsOnly_abstract1]

theorem Expr.forallDomainsOnly_abstractN (n : Nat) (source : Expr) (xs : List FVarId) (k : Nat) :
    Expr.forallDomainsOnly n (source.abstractN xs k) =
      (Expr.forallDomainsOnly n source).abstractN xs k := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    cases source <;> simp [Expr.forallDomainsOnly, Expr.abstractN, ih]
    all_goals split <;> rfl

theorem LocalContext.forallDomainsOnly_foldN
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (body : Expr) :
    Expr.forallDomainsOnly fvars.length
      (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) body) =
      fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) (.sort .zero) := by
  induction fvars with
  | nil => rfl
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    simp only [List.foldr_cons, List.length_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.forallDomainsOnly, Expr.forallDomainsOnly_abstractN]
    simpa only [LocalContext.mkBindingList1N, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun e => Expr.forallE name (type.abstractN []) (e.abstractN [fv]) bi)
        (ih (fun other hother => hdecl other (by simp [hother])))

theorem FVarArrayIn.forallDomainsOnly
    (H : FVarArrayIn c xs) (Hc : BindingContextWF c)
    (hnodup : H.fvars.Nodup) (body : Expr) :
    Expr.forallDomainsOnly xs.size (c.lctx.mkForall xs body) =
      c.lctx.mkForall xs (.sort .zero) := by
  have hsize : xs.size = H.fvars.length := by
    simpa using congrArg Array.size H.expressions
  have hdecl : ∀ fv ∈ H.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    exact Hc.findCDecl fv (H.members fv hfv)
  have hfind : ∀ fv ∈ H.fvars, ∃ decl, c.lctx.find? fv = some decl := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h⟩ := hdecl fv hfv
    exact ⟨_, h⟩
  conv => lhs; rw [H.expressions]
  conv => rhs; rw [H.expressions]
  simp only [List.size_toArray, List.length_map]
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  exact LocalContext.forallDomainsOnly_foldN hdecl body

theorem RecursorConstruction.indexDomainSource_eq
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    H.indexDomainSource owner =
      (H.localContext.lctx.mkForall H.recInfos[owner]!.indices (.sort .zero)).abstractList
        H.params.fvars := by
  let I := H.bindings.indices owner howner
  have hindices : I.fvars.Nodup :=
    (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts.indices
  rw [indexDomainSource, Expr.forallDomainsOnly_abstractList,
    I.forallDomainsOnly H.localWF hindices]

/-- The executable index telescope mentions only the declaration's universe parameters: the
construction records the index-universe check of the motive pass, and context extension and
parameter abstraction preserve it. -/
theorem RecursorConstruction.indexDomainSource_levelParams
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    (H.indexDomainSource owner).levelParamsIn c.lparams = true := by
  obtain ⟨S, _⟩ := H.motiveTelescopes.motiveDecls owner howner
  have hsource := S.indexUniverses
  rw [H.localExtends.lparams_eq] at hsource
  rw [H.indexDomainSource_eq owner howner, Expr.levelParamsIn_abstractList]
  exact hsource

theorem RecursorConstruction.chooseDeclUnivIndexDomains_large
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (helim : H.elimLevel = .param fresh) :
    ∃ sourceDomains,
      sourceDomains.length = H.recInfos[owner]!.indices.size ∧
      TrExprS R.context.venv c.lparams
        (abstractForallContext R.parameterScope.toCtx.reverse [])
        (H.indexDomainSource owner) (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      TrExprS R.context.venv (fresh :: c.lparams)
        ((abstractForallContext R.parameterScope.toCtx.reverse []).instL
          (VLevel.prependShift c.lparams.length))
        (H.indexDomainSource owner)
        (VExpr.wrapForalls (sourceDomains.map (VExpr.instL (VLevel.prependShift c.lparams.length)))
          (.sort .zero)) := by
  obtain ⟨S, indices, major, level, hindices, hlevel, Htr, _, _⟩ :=
    H.unannotatedMotiveDomains owner howner
  have Htel := (S.indicesBound.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
      H.params.fvars
  have hfresh : fresh ∉ c.lparams := by
    simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
  have hsource := levelParamsIn_fixed_dropFresh
    (H.indexDomainSource_levelParams owner howner) hfresh
  have Hctx := H.parameterAnonymousContext
  have hlevels : recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible =
      VLevel.prependShift c.lparams.length := by
    have hgeneral : ∀ elim (ha : AddInductive.AdmissibleElimLevel c.lparams elim),
        elim = .param fresh → recursorDeclarationAbstractLevels c.lparams ha =
          VLevel.prependShift c.lparams.length := by
      intro elim ha heq
      subst elim
      simp only [recursorDeclarationAbstractLevels]
      exact VLevel.inst_map_id VLevel.prependShift_length
    exact hgeneral _ _ helim
  have Hctx' : abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [] =
      (abstractForallContext R.parameterScope.toCtx.reverse []).instL
        (VLevel.prependShift c.lparams.length) := by
    simpa only [hlevels] using Hctx
  rw [Hctx', H.recursorEnv] at Htr
  have Htr' : TrExprS R.context.venv (fresh :: c.lparams)
      ((abstractForallContext R.parameterScope.toCtx.reverse []).instL
        (VLevel.prependShift c.lparams.length))
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      (VExpr.wrapForalls indices (.forallE major (.sort level))) := by
    simpa [helim, AddInductive.getRecLevelParams] using Htr
  have Hchosen := TrExprS.chooseDeclUnivForallDomains R.context.checking.tr.wf
    R.sourceAnonymousParameterWF hfresh Htel hindices Htr' hsource
  simpa only [indexDomainSource, abstractForallContext_toCtx, List.reverse_reverse,
    VLCtx.toCtx, List.append_nil] using Hchosen

/-- For elimination into `Prop` the recursor's universe parameters are the source ones, so the
index domains of the executable motive translate directly in the recursor-checking environment
over the source parameter scope. -/
theorem RecursorConstruction.chooseDeclUnivIndexDomains_small
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (helim : H.elimLevel = .zero) :
    ∃ sourceDomains,
      sourceDomains.length = H.recInfos[owner]!.indices.size ∧
      TrExprS R.context.venv c.lparams
        (abstractForallContext R.parameterScope.toCtx.reverse [])
        (H.indexDomainSource owner) (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls sourceDomains (.sort .zero)) := by
  obtain ⟨S, indices, major, level, hindices, hlevel, Htr, _, _⟩ :=
    H.unannotatedMotiveDomains owner howner
  have Htel := (S.indicesBound.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
      H.params.fvars
  obtain ⟨Hprefix, Htype⟩ := TrExprS.forallDomainsOnly Htel hindices Htr
  have hlevels : recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible =
      VLevel.params c.lparams.length := by
    have hgeneral : ∀ elim (ha : AddInductive.AdmissibleElimLevel c.lparams elim),
        elim = .zero → recursorDeclarationAbstractLevels c.lparams ha =
          VLevel.params c.lparams.length := by
      intro elim ha heq
      subst elim
      rfl
    exact hgeneral _ _ helim
  have Hctx := H.parameterAnonymousContext
  rw [hlevels, R.sourceAnonymousParameterWF.instL_id] at Hctx
  rw [Hctx, H.recursorEnv] at Hprefix Htype
  exact ⟨indices, hindices, by simpa only [indexDomainSource,
    helim, AddInductive.getRecLevelParams] using Hprefix, by
    simpa only [abstractForallContext_toCtx, List.reverse_reverse, VLCtx.toCtx,
      List.append_nil, helim, AddInductive.getRecLevelParams] using Htype⟩

end Lean4Lean.VerifyInductive
