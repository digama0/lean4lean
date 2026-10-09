import Lean4Lean.Verify.Inductive.Rules.Alignment

/-! The context of a rule's selected minor premise: the generated recursor and the motive
reconstructed by the motive pass share one parameter context, the generated recursor domain at
the rule's flattened minor slot is the type recorded by the minor pass, and the parameters,
motives and earlier minors form a dependency-selected free-variable scope built from the
closed translation of the generated recursor type. Also general lemmas on lambda contexts
(`VLCtx`) and forall telescope translations. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

open checkInductiveTypes.loopType

/-- Instantiating an abstracted free variable with itself restores the
expression. -/
theorem Expr.instantiate1'_abstract1_self (v : FVarId) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 v k).instantiate1' (.fvar v) k = e
  | .bvar i, k => by
    simp only [Expr.abstract1, Expr.instantiate1']
    by_cases h : i < k
    · simp [h]
    · have h1 : ¬ i + 1 < k := by omega
      have h2 : i + 1 ≠ k := by omega
      simp [h, h1, h2]
  | .fvar w, k => by
    by_cases h : v = w
    · subst h
      simp [Expr.abstract1, Expr.instantiate1', Expr.liftLooseBVars']
    · have : (v == w) = false := by simpa using h
      simp [Expr.abstract1, Expr.instantiate1', this]
  | .mdata m e, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v e k]
  | .proj s i e, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v e k]
  | .app f a, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v f k,
      Expr.instantiate1'_abstract1_self v a k]
  | .lam n t b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .forallE n t b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .letE n t val b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v val k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .const .., _ | .sort _, _ | .mvar _, _ | .lit _, _ => by
    simp [Expr.abstract1, Expr.instantiate1']

/-- The annotation-only `inferImplicit` pass can be erased from the concrete
side of a forall telescope translation. -/
theorem Expr.ForallTelescopeTypeTranslation.of_inferImplicit
    {env : VEnv} {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {n : Nat} {e' : VExpr} (numParams : Nat)
      (considerRange : Bool),
      Expr.ForallTelescopeTypeTranslation env Us Δ
        (e.inferImplicit numParams considerRange) n e' →
      Expr.ForallTelescopeTypeTranslation env Us Δ e n e'
  | Δ, e, n, e', 0, cr, H => by simpa [Expr.inferImplicit] using H
  | Δ, e, n, e', numParams + 1, cr, H => by
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.inferImplicit] at H
      cases H with
      | nil Htr Htype => exact .nil (TrExprS.of_inferImplicit (numParams := numParams + 1)
          (considerRange := cr) (by simpa [Expr.inferImplicit] using Htr)) Htype
      | cons Hdom HdomType Hbody =>
        exact .cons Hdom HdomType
          (Expr.ForallTelescopeTypeTranslation.of_inferImplicit numParams cr Hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- Instantiate an abstracted binder of a forall telescope translation with
its free variable. -/
theorem Expr.ForallTelescopeTypeTranslation.instantiateFVar
    {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} (hfresh : v₀ ∉ Δ₀.fvars) :
    ∀ {dk k : Nat} {Δ₁ Δ : VLCtx} {e : Expr} {n : Nat} {e' : VExpr},
      VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ →
      Expr.ForallTelescopeTypeTranslation env Us Δ e n e' →
      Expr.ForallTelescopeTypeTranslation env Us Δ₁
        (e.instantiate1' (.fvar v₀) dk) n e'
  | _, _, _, _, _, _, _, W, .nil Htr Htype =>
    .nil (TrExprS.instantiateFVar W hfresh Htr) (W.toCtx ▸ Htype)
  | _, _, _, _, _, _, _, W, .cons Hdom HdomType Hbody => by
    simp only [Expr.instantiate1']
    exact .cons (TrExprS.instantiateFVar W hfresh Hdom) (W.toCtx ▸ HdomType)
      (Expr.ForallTelescopeTypeTranslation.instantiateFVar hfresh W.succ Hbody)


/-- Peel the outermost binder of a local-context forall. -/
theorem LocalContext.mkForall_cons_cdecl {lctx : LocalContext}
    {x : FVarId} {xs : List FVarId} {b : Expr}
    {idx : Nat} {n : Name} {ty : Expr} {bi : BinderInfo} {kind : LocalDeclKind}
    (hx : lctx.find? x = some (.cdecl idx x n ty bi kind))
    (hxs : ∀ y ∈ xs, ∃ d, lctx.find? y = some d)
    (nd : (x :: xs).Nodup) (hb : Closed b) (hclosed : LocalContext.LctxClosed lctx) :
    lctx.mkForall ((x :: xs).map Expr.fvar).toArray b =
      .forallE n ty ((lctx.mkForall (xs.map Expr.fvar).toArray b).abstract1 x) bi := by
  have hex : ∀ y ∈ x :: xs, ∃ d, lctx.find? y = some d := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, hx⟩
    · exact hxs y hy
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq' hex nd hb hclosed.declsClosed,
    LocalContext.mkBindingList_cons hxs nd, LocalContext.mkForall,
    LocalContext.mkBinding_eq' hxs (List.nodup_cons.mp nd).2 hb hclosed.declsClosed]
  simp [LocalContext.mkBindingList1, hx]

/-- Nested local-context foralls over disjoint lists combine. -/
theorem LocalContext.mkForall_mkForall {lctx : LocalContext}
    {xs ys : List FVarId} {b : Expr}
    (hex : ∀ y ∈ xs ++ ys, ∃ d, lctx.find? y = some d)
    (nd : (xs ++ ys).Nodup) (hb : Closed b) (hclosed : LocalContext.LctxClosed lctx) :
    lctx.mkForall (xs.map Expr.fvar).toArray
        (lctx.mkForall (ys.map Expr.fvar).toArray b) =
      lctx.mkForall ((xs ++ ys).map Expr.fvar).toArray b := by
  have hexY : ∀ y ∈ ys, ∃ d, lctx.find? y = some d :=
    fun y hy => hex y (List.mem_append_right _ hy)
  have hexX : ∀ y ∈ xs, ∃ d, lctx.find? y = some d :=
    fun y hy => hex y (List.mem_append_left _ hy)
  have ndY := (List.nodup_append.mp nd).2.1
  have ndX := (List.nodup_append.mp nd).1
  obtain ⟨hinner, hinnerClosed⟩ := LocalContext.mkBindingListN_eq_mkBindingList
    (isLambda := false) hexY ndY hb hclosed.declsClosed
  have hinner' : lctx.mkForall (ys.map Expr.fvar).toArray b =
      LocalContext.mkBindingList false lctx ys b := by
    rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
    exact hinner
  rw [hinner', LocalContext.mkForall,
    LocalContext.mkBinding_eq' hexX ndX hinnerClosed hclosed.declsClosed,
    LocalContext.mkForall, LocalContext.mkBinding_eq' hex nd hb hclosed.declsClosed,
    LocalContext.mkBindingList_append hex nd]

/-- A dependency-selected prefix of an all-lambda context, built from a
closed translation of the forall over that prefix.  Each retained domain is
the corresponding domain of the closed translation with its binders
instantiated by the selected free variables, so no runtime translation is
restricted. -/
theorem MLCtxOnlyLams.closedTelescopeScope
    {c : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : MLCtxOnlyLams c) (henv : env.WF) (Hwf : c.WF env Us)
    (outer : List FVarId) (body : Expr) (k : Nat)
    (hdecls : ∀ fv ∈ outer, ∃ d, c.lctx.find? fv = some d)
    (hnodup : outer.Nodup) (hbody : Closed body)
    (hfilter : c.vlctx.fvars.filter (· ∈ outer) = outer.reverse)
    (hup : IsFVarUpSet (· ∈ outer) c.vlctx)
    {tgt : VExpr}
    (HT : Expr.ForallTelescopeTypeTranslation env Us []
      (c.lctx.mkForall (outer.map Expr.fvar).toArray body)
      (outer.length + k) tgt) :
    ∃ scope, ∃ Hscope : ScopeEmbedding env Us scope c.vlctx,
      scope.fvars = outer.reverse ∧
      Hscope.shift = fvarSelectionLift c.vlctx.fvars (· ∈ outer) ∧
      (∀ body', Hscope.sourceTelescope.closeSource body' =
        c.lctx.mkForall (outer.map Expr.fvar).toArray body') ∧
      ∃ t', Expr.ForallTelescopeTypeTranslation env Us scope body k t' ∧
        tgt = VExpr.wrapForalls scope.toCtx.reverse t' := by
  have hclosedL : LocalContext.LctxClosed c.lctx := Hwf.tr.lctxClosed
  let E : Nat → Expr := fun m =>
    c.lctx.mkForall ((outer.drop m).map Expr.fvar).toArray body
  let Good : VLCtx → Prop := fun ts =>
    ∃ m, m ≤ outer.length ∧ ts.fvars = (outer.take m).reverse ∧
      ∃ t', Expr.ForallTelescopeTypeTranslation env Us ts (E m)
          (outer.length - m + k) t' ∧
        tgt = VExpr.wrapForalls ts.toCtx.reverse t'
  have hgood0 : Good [] :=
    ⟨0, Nat.zero_le _, by simp, tgt, by simpa [E] using HT,
      by simp [VExpr.wrapForalls, VLCtx.toCtx]⟩
  have oracle : ∀ (ts : VLCtx) (fv : FVarId) (type : Expr),
      Good ts → (fv :: ts.fvars) <:+ outer.reverse →
      (∃ idx name bi kind,
        c.lctx.find? fv = some (.cdecl idx fv name type bi kind)) →
      FVarsIn (· ∈ ts.fvars) type → Closed type →
      ∃ t, TrExprS env Us ts type t ∧
        env.IsType Us.length ts.toCtx t ∧
        Good ((some (fv, type.fvarsList), .vlam t) :: ts) := by
    intro ts fv type hgood hsuf hdecl _ _
    obtain ⟨m, hm, hfvs, t', HE, htgt⟩ := hgood
    obtain ⟨idx, name, bi, kind, hfind⟩ := hdecl
    have hpre : outer.take m ++ [fv] <+: outer := by
      rw [hfvs] at hsuf
      have : ((outer.take m) ++ [fv]).reverse <:+ outer.reverse := by
        simpa using hsuf
      exact List.reverse_suffix.mp this
    have hlenpre := hpre.length_le
    simp only [List.length_append, List.length_take, List.length_singleton] at hlenpre
    have hmlt : m < outer.length := by omega
    have hget : outer[m]'hmlt = fv := by
      have h := hpre.getElem (i := m) (by simp [Nat.min_eq_left hm])
      rw [← h]
      simp [List.getElem_append_right, Nat.min_eq_left hm]
    have hdrop : outer.drop m = fv :: outer.drop (m + 1) := by
      rw [List.drop_eq_getElem_cons hmlt, hget]
    have hnd' : (fv :: outer.drop (m + 1)).Nodup := by
      rw [← hdrop]
      exact (List.drop_sublist m outer).nodup hnodup
    have hxs : ∀ y ∈ outer.drop (m + 1), ∃ d, c.lctx.find? y = some d :=
      fun y hy => hdecls y (List.mem_of_mem_drop hy)
    have hpeel : E m = .forallE name type ((E (m + 1)).abstract1 fv) bi := by
      simp only [E]
      rw [hdrop]
      exact LocalContext.mkForall_cons_cdecl hfind hxs hnd' hbody hclosedL
    have hcount : outer.length - m + k =
        (outer.length - (m + 1) + k) + 1 := by omega
    rw [hpeel, hcount] at HE
    cases HE with
    | @cons _ _ dom' _ _ t'' _ _ Hdom HdomType Hbody =>
    have hfresh : fv ∉ ts.fvars := by
      rw [hfvs]
      intro hmem
      have hmem' := List.mem_reverse.mp hmem
      have hsplit : outer = outer.take m ++ fv :: outer.drop (m + 1) := by
        rw [← hdrop, List.take_append_drop]
      have hndOuter := hnodup
      rw [hsplit] at hndOuter
      exact (List.nodup_append.mp hndOuter).2.2 fv hmem' fv (by simp) rfl
    have W : VLCtx.Abstract ts fv (.vlam dom') 0 0
        ((some (fv, type.fvarsList), .vlam dom') :: ts)
        ((none, .vlam dom') :: ts) := .zero
    have Hnext := Expr.ForallTelescopeTypeTranslation.instantiateFVar
      hfresh W Hbody
    rw [Expr.instantiate1'_abstract1_self] at Hnext
    refine ⟨dom', Hdom, HdomType, m + 1, hmlt, ?_, t'', Hnext, ?_⟩
    · simp only [VLCtx.fvars_cons_some, hfvs]
      rw [List.take_succ_eq_append_getElem hmlt, hget]
      simp
    · rw [htgt]
      simp [VLCtx.toCtx, VExpr.wrapForalls]
  have hL : c.vlctx.fvars.filter (· ∈ outer) <:+ outer.reverse := by
    rw [hfilter]
    exact List.suffix_refl _
  obtain ⟨scope, Hscope, hscopeFVars, hshift, _hdeclsScope, hclose,
      m, hm, hfvm, t', HE, htgt⟩ :=
    MLCtxOnlyLams.scopedFVarsSourceOracle H henv Hwf (· ∈ outer) hup Good hgood0 hL
      (Lctx := c.lctx) (fun _ _ h => h) oracle
  have hscopeOuter : scope.fvars = outer.reverse := hscopeFVars.trans hfilter
  have hmEq : m = outer.length := by
    have h := congrArg List.length (hfvm.symm.trans hscopeOuter)
    simp at h
    omega
  subst hmEq
  refine ⟨scope, Hscope, hscopeOuter, hshift, ?_, t', ?_, htgt⟩
  · intro body'
    rw [hclose body', hscopeOuter, List.reverse_reverse]
  · have hdl : outer.drop outer.length = [] := List.drop_length
    simp only [E, hdl, List.map_nil, Nat.sub_self, Nat.zero_add] at HE
    simpa [LocalContext.mkForall_empty] using HE

/-- The generated recursor and the independently replayed canonical motive
share the same parameter context.  This is the first direct link from the
five-group executable telescope to the permutation-free semantic telescope;
subsequent index alignment can therefore work under either parameter list
without reusing an executable `isDefEq` success as an assumption. -/
theorem RecursorCheck.installedPairedParameterAlignmentAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.installedRecursorParameterContextAt owner howner with
    ⟨T, hgenerated⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.motiveDecls owner hrecInfo with ⟨S, hcanonical⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  refine ⟨T, S, ?_⟩
  exact VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
    hgenerated ((hcanonical.mono hbase).symm H.outVEnvWF.ordered)

/-- Executable/canonical owner-motive comparison frame.  This packages
the independently replayed canonical motive with the exact source domain and
abstract target selected from the installed generated recursor.  The target
domain is checked under parameters and strictly earlier motives only; hence
the remaining comparison with `C.motiveType` is a context-transport problem,
not another inversion of the executable telescope. -/
theorem
    RecursorCheck.installedOwnerMotiveFrameAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ D : FVarDeclAt H.localContext
            (H.recInfos.map (·.motive)) owner,
          D.type = H.origins.motiveTypes[owner]! ∧
          D.type = H.localContext.lctx.mkForall
            H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel)) ∧
          ∃ (suffixSource : Expr) (name : Name)
            (sourceDomain sourceBody : Expr) (bi : BinderInfo)
            (_bodyTarget : VExpr),
            Expr.ForallTelescope
              (H.generated.entry owner howner).info.type
              (T.params.length + owner) suffixSource ∧
            suffixSource = .forallE name sourceDomain sourceBody bi ∧
            sourceDomain = D.type.abstractList
              (H.params.fvars ++ H.bindings.motives.fvars.take owner) ∧
            TrExprS H.outVEnv Us
              (abstractForallContext
                (T.params ++ T.motives.take owner) [])
              sourceDomain T.motives[owner]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                (T.params ++ T.motives.take owner) []).toCtx
              T.motives[owner]! := by
  dsimp only
  rcases H.installedPairedParameterAlignmentAt owner howner with
    ⟨T, S, hparameters⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hmotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hrecInfo
  have hmotiveArray : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hrecInfo
  rcases H.origins.motives.declaration owner hmotiveArray with
    ⟨D, hdeclarationOrigin⟩
  have hdeclarationShape : D.type = H.localContext.lctx.mkForall
      H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)) :=
    hdeclarationOrigin.trans (H.motiveShapes.shape owner hrecInfo)
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have HoriginBinder :=
    selections.ownerMotiveBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
  have HoriginBinderStats : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (stats.params.size + owner)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner)) := by
    rw [(H.generated.entry owner howner).type]
    simpa [selections, RecInfoBindings.toRecursorBinderGroups,
      FVarArrayIn.toCDeclArray] using HoriginBinder
  have HoriginBinder' : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (T.params.length + owner)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner)) := by
    simpa [T.params_length] using HoriginBinderStats
  rcases T.ownerMotiveBinder hmotive with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType⟩
  have HsourceBinder := Hsource.binderAt hsource
  have hsourceDomain : sourceDomain = D.type.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars.take owner) := by
    have heq := HsourceBinder.unique HoriginBinder'
    simpa [selections, RecInfoBindings.toRecursorBinderGroups] using heq
  exact ⟨T, S, hparameters, D, hdeclarationOrigin, hdeclarationShape,
    suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, hsourceDomain,
    by simpa [getElem!_pos T.motives owner hmotive] using Hdomain,
    by simpa [getElem!_pos T.motives owner hmotive] using HdomainType⟩

/-- Reduced owner-motive comparison with all positional witnesses rewritten
away.  The left side is the exact executable declaration shape closed
over the source binders corresponding to the target context on the right.
This is the form needed for the comparison with `C.motiveType`. -/
theorem
    RecursorCheck.installedOwnerMotiveDomainTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives.take owner) [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel))).abstractList
                (H.params.fvars ++ H.bindings.motives.fvars.take owner))
          T.motives[owner]! ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (T.params ++ T.motives.take owner) []).toCtx
          T.motives[owner]! := by
  dsimp only
  rcases H.installedOwnerMotiveFrameAt owner howner with
    ⟨T, S, hparameters, D, _hdeclarationOrigin, hdeclarationShape,
      suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      _Hsource, _hsource, hsourceDomain, Hdomain, HdomainType⟩
  rw [hsourceDomain, hdeclarationShape] at Hdomain
  exact ⟨T, S, hparameters, Hdomain, HdomainType⟩

/-- Recursor-environment identification of the generated recursor domain at
this rule's flattened minor slot.  The source selected structurally from the
translated recursor is exactly the declaration type recorded by the second
`mkRecInfos` pass, closed over parameters, motives, and earlier minors. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorDomain
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ D : FVarDeclAt H.localContext
          (H.recInfos.flatMap (·.minors)) minorIdx,
        ∃ _O : H.origins.FlatMinorBinderType D,
          ∃ _S : MinorPremiseType,
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          TrExprS H.outVEnv Us
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])
              (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
              T.minors[minorIdx]! := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases H.installedRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorArray :
      minorIdx < (H.recInfos.flatMap (·.minors)).size :=
    A.rule.minor_valid
  rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx
      hminorArray with ⟨D⟩
  rcases H.origins.flatMinorBinderType D with ⟨O⟩
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have HoriginBinder := selections.minorBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
  have HoriginBinderStats : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (stats.params.size + (H.recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx)) := by
    rw [(H.generated.entry owner howner).type]
    simpa [selections,
      RecInfoBindings.toRecursorBinderGroups,
      FVarArrayIn.toCDeclArray, List.append_assoc] using
      HoriginBinder
  have HoriginBinder' : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (T.params.length + T.motives.length + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx)) := by
    simpa [T.params_length, T.motives_length, Nat.add_assoc] using
      HoriginBinderStats
  rcases T.minorBinder minorIdx hminor with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType⟩
  have HsourceBinder := Hsource.binderAt hsource
  have hsourceDomain : sourceDomain = D.type.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take minorIdx) := by
    exact HsourceBinder.unique HoriginBinder'
  rw [hsourceDomain] at Hdomain
  exact ⟨T, D, O, S, by
    simpa [minorIdx, getElem!_pos T.minors minorIdx hminor] using Hdomain,
    by simpa [minorIdx, getElem!_pos T.minors minorIdx hminor] using HdomainType⟩

/-- The parameters, motives, and an arbitrary initial minor segment form a
dependency-closed subset of the interleaved recursor context.  The proof
reads each declaration's domain from the fully closed generated recursor
telescope, so skipped indices and majors cannot enter the retained set. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorPrefixUp
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (minorLimit : Nat)
    (hminorLimit : minorLimit ≤ H.bindings.flatMinors.fvars.length) :
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorLimit
    IsFVarUpSet (fun fv => fv ∈ sourceBinders)
      H.recursorWF.mlctx.vlctx := by
  dsimp only
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorLimit
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hselectionParams : selections.params.fvars = H.params.fvars := rfl
  have hselectionMotives :
      selections.motives.fvars = H.bindings.motives.fvars := rfl
  have hselectionMinors :
      selections.minors.fvars = H.bindings.flatMinors.fvars := rfl
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  rcases H.installedRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  have HsourceClosed :
      (H.generated.entry owner howner).info.type.FVarsIn
        (fun _ => False) := by
    have Hscope := T.typed.translation.fvarsIn
    exact Hscope.mono fun fv hfv => by simp at hfv
  have Hcontext := H.recursorWF.mlctx_wf.tr
  rw [H.recursorWF.lctx_eq] at Hcontext
  apply checkInductiveTypes.loopType.TrLCtx'.isFVarUpSet Hcontext.2
  intro d hd hselected dep hdep
  change d.fvarId ∈ sourceBinders at hselected
  rcases List.mem_append.mp hselected with hprefix | hminor
  · rcases List.mem_append.mp hprefix with hparam | hmotive
    · rcases List.mem_iff_getElem.mp hparam with ⟨idx, hidx, hget⟩
      have hi : idx < stats.params.size := by
        rw [← H.params.length_fvars]
        exact hidx
      rcases H.params.declarationAt H.localWF idx hi with ⟨D⟩
      rcases H.params.getElem_eq_fvar idx hi with ⟨_hidxFVars, hexpr⟩
      have hDfv : D.fvar = d.fvarId := by
        apply Expr.fvar.inj
        calc
          .fvar D.fvar = stats.params[idx] := D.expression.symm
          _ = .fvar H.params.fvars[idx] := hexpr
          _ = .fvar d.fvarId := congrArg Expr.fvar hget
      have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
      have Hbinder := selections.parameterBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
      dsimp only at Hbinder
      rw [← (H.generated.entry owner howner).type] at Hbinder
      have Hclosed := Hbinder.domainFVarsIn HsourceClosed
      have Htype := FVarsIn.of_abstractList Hclosed
      have HtypeScope : D.type.FVarsIn (fun fv => fv ∈ sourceBinders) :=
        Htype.mono fun fv hfv => by
          rcases hfv with hfv | hfalse
          · exact List.mem_append_left _
              (List.mem_append_left _ (List.mem_of_mem_take hfv))
          · exact False.elim hfalse
      rw [hdEq] at hdep
      exact (fvarsIn_iff.mp HtypeScope).1 dep hdep
    · rcases List.mem_iff_getElem.mp hmotive with ⟨idx, hidx, hget⟩
      have hi : idx < (H.recInfos.map (·.motive)).size := by
        rw [← H.bindings.motives.length_fvars]
        exact hidx
      rcases H.bindings.motives.declarationAt H.localWF idx hi with ⟨D⟩
      rcases H.bindings.motives.getElem_eq_fvar idx hi with
        ⟨_hidxFVars, hexpr⟩
      have hDfv : D.fvar = d.fvarId := by
        apply Expr.fvar.inj
        calc
          .fvar D.fvar = (H.recInfos.map (·.motive))[idx] :=
            D.expression.symm
          _ = .fvar H.bindings.motives.fvars[idx] := hexpr
          _ = .fvar d.fvarId := congrArg Expr.fvar hget
      have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
      have Hbinder := selections.motiveBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
      dsimp only at Hbinder
      rw [← (H.generated.entry owner howner).type] at Hbinder
      have Hclosed := Hbinder.domainFVarsIn HsourceClosed
      have Htype := FVarsIn.of_abstractList Hclosed
      have HtypeScope : D.type.FVarsIn
          (fun fv => fv ∈ sourceBinders) :=
        Htype.mono fun fv hfv => by
          rcases hfv with hfv | hfalse
          · rcases List.mem_append.mp hfv with hparam | hmotive
            · exact List.mem_append_left _ (List.mem_append_left _ hparam)
            · exact List.mem_append_left _
                (List.mem_append_right _ (List.mem_of_mem_take hmotive))
          · exact False.elim hfalse
      rw [hdEq] at hdep
      exact (fvarsIn_iff.mp HtypeScope).1 dep hdep
  · rcases List.mem_iff_getElem.mp hminor with ⟨idx, hidxTake, hgetTake⟩
    have htakeLength :
        (H.bindings.flatMinors.fvars.take minorLimit).length = minorLimit := by
      simp [Nat.min_eq_left hminorLimit]
    have hidxMinor : idx < minorLimit := by
      rw [htakeLength] at hidxTake
      exact hidxTake
    have hidx : idx < H.bindings.flatMinors.fvars.length :=
      Nat.lt_of_lt_of_le hidxMinor hminorLimit
    have hget : H.bindings.flatMinors.fvars[idx] = d.fvarId := by
      simpa using hgetTake
    have hi : idx < (H.recInfos.flatMap (·.minors)).size := by
      rw [← H.bindings.flatMinors.length_fvars]
      exact hidx
    rcases H.bindings.flatMinors.declarationAt H.localWF idx hi with ⟨D⟩
    rcases H.bindings.flatMinors.getElem_eq_fvar idx hi with
      ⟨_hidxFVars, hexpr⟩
    have hDfv : D.fvar = d.fvarId := by
      apply Expr.fvar.inj
      calc
        .fvar D.fvar = (H.recInfos.flatMap (·.minors))[idx] :=
          D.expression.symm
        _ = .fvar H.bindings.flatMinors.fvars[idx] := hexpr
        _ = .fvar d.fvarId := congrArg Expr.fvar hget
    have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
    have Hbinder := selections.minorBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
    dsimp only at Hbinder
    rw [← (H.generated.entry owner howner).type] at Hbinder
    have Hclosed := Hbinder.domainFVarsIn HsourceClosed
    have Htype := FVarsIn.of_abstractList Hclosed
    have HtypeScope : D.type.FVarsIn
        (fun fv => fv ∈ sourceBinders) :=
      Htype.mono fun fv hfv => by
        rcases hfv with hfv | hfalse
        · rw [hselectionParams, hselectionMotives,
              hselectionMinors] at hfv
          rcases List.mem_append.mp hfv with hprefix | hprior
          · rcases List.mem_append.mp hprefix with hparam | hmotive
            · exact List.mem_append_left _ (List.mem_append_left _ hparam)
            · exact List.mem_append_left _
                (List.mem_append_right _ hmotive)
          · exact List.mem_append_right _
              ((List.take_sublist_take_left
                (Nat.le_of_lt hidxMinor)).subset hprior)
        · exact False.elim hfalse
    rw [hdEq] at hdep
    exact (fvarsIn_iff.mp HtypeScope).1 dep hdep

/-- The parameters, motives, and strictly earlier minors selected by one
generated minor form a dependency-closed subset of the interleaved recursor
context. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorPrefixUp
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    IsFVarUpSet (fun fv => fv ∈ sourceBinders)
      H.recursorWF.mlctx.vlctx := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  apply RecursorCheck.RuleAlignment.installedMinorPrefixUp
    (H := H) (owner := owner) (howner := howner) minorIdx
  rw [H.bindings.flatMinors.length_fvars]
  exact Nat.le_of_lt A.rule.minor_valid

/-- Two lambda contexts with the same binder keys and definitionally equal
domains are aligned. -/
theorem VLCtx.IsDefEq.ofKeysCtx {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : VLCtx}, Δ₁.map Prod.fst = Δ₂.map Prod.fst →
      (∀ e ∈ Δ₁, ∃ k d, e = (k, .vlam d)) →
      (∀ e ∈ Δ₂, ∃ k d, e = (k, .vlam d)) →
      VLCtx.WF env U Δ₁ →
      VEnv.IsDefEqCtx env U [] Δ₁.toCtx Δ₂.toCtx →
      VLCtx.IsDefEq env U Δ₁ Δ₂
  | [], [], _, _, _, _, _ => .nil
  | [], _ :: _, h, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _ => by simp at h
  | e₁ :: t₁, e₂ :: t₂, hk, h1, h2, hwf, hctx => by
    obtain ⟨k₁, a, rfl⟩ := h1 e₁ (by simp)
    obtain ⟨k₂, b, rfl⟩ := h2 e₂ (by simp)
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨rfl, hk'⟩ := hk
    have hctx' : VEnv.IsDefEqCtx env U [] (a :: VLCtx.toCtx t₁) (b :: VLCtx.toCtx t₂) := by
      simpa [VLCtx.toCtx] using hctx
    cases hctx' with
    | succ htail hab =>
      exact .cons (VLCtx.IsDefEq.ofKeysCtx hk'
        (fun e he => h1 e (by simp [he])) (fun e he => h2 e (by simp [he]))
        hwf.1 htail) hwf.2.1 (.vlam hab)

theorem VLCtx.IsDefEq.keys_eq {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : VLCtx}, VLCtx.IsDefEq env U Δ₁ Δ₂ → Δ₁.map Prod.fst = Δ₂.map Prod.fst
  | _, _, .nil => rfl
  | _, _, .cons h _ _ => by simp [VLCtx.IsDefEq.keys_eq h]

theorem VLCtx.FVLift'.keys_sublist {Δ Δ' : VLCtx} {dk k : Nat} {n : Lift}
    (W : VLCtx.FVLift' Δ Δ' dk n k) : Δ.map Prod.fst <+ Δ'.map Prod.fst := by
  induction W with
  | refl => exact .refl _
  | skip_fvar _ _ _ ih => exact .cons _ ih
  | cons_fvar _ _ _ _ ih => exact .cons_cons _ ih
  | cons_bvar _ _ ih => exact .cons_cons _ ih

theorem VLCtx.mem_fvars_of_key : ∀ {L : VLCtx} {fv : FVarId} {d : List FVarId},
    some (fv, d) ∈ L.map Prod.fst → fv ∈ L.fvars
  | [], _, _, h => by simp at h
  | (none, _) :: L, _, _, h => by
    simp only [List.map_cons, List.mem_cons, reduceCtorEq, false_or] at h
    exact VLCtx.mem_fvars_of_key (L := L) h
  | (some (fv', d'), _) :: L, fv, d, h => by
    simp only [List.map_cons, List.mem_cons, Option.some.injEq, Prod.mk.injEq] at h
    simp only [VLCtx.fvars_cons_some, List.mem_cons]
    rcases h with ⟨rfl, _⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (VLCtx.mem_fvars_of_key h)

/-- In a context with distinct free variables, a free variable determines
its declaration key. -/
theorem VLCtx.key_unique : ∀ {L : VLCtx}, L.fvars.Nodup →
    ∀ {fv : FVarId} {d₁ d₂ : List FVarId},
      some (fv, d₁) ∈ L.map Prod.fst → some (fv, d₂) ∈ L.map Prod.fst → d₁ = d₂
  | [], _, _, _, _, h, _ => by simp at h
  | (none, _) :: L, hnd, _, _, _, h1, h2 => by
    simp only [List.map_cons, List.mem_cons, reduceCtorEq, false_or] at h1 h2
    exact VLCtx.key_unique (L := L) hnd h1 h2
  | (some (fv', d'), _) :: L, hnd, fv, d₁, d₂, h1, h2 => by
    simp only [VLCtx.fvars_cons_some, List.nodup_cons] at hnd
    simp only [List.map_cons, List.mem_cons, Option.some.injEq, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨h2a, rfl⟩ | h2
    · rfl
    · exact absurd (VLCtx.mem_fvars_of_key h2) hnd.1
    · exact absurd (h2a ▸ VLCtx.mem_fvars_of_key h1) hnd.1
    · exact VLCtx.key_unique hnd.2 h1 h2

/-- Two selections of free-variable keys from one context agree when they
select the same free variables. -/
theorem VLCtx.keys_eq_of_fvars {L : VLCtx} (hnd : L.fvars.Nodup) :
    ∀ {A B : List (Option (FVarId × List FVarId))},
      (∀ x ∈ A, x ∈ L.map Prod.fst) → (∀ x ∈ B, x ∈ L.map Prod.fst) →
      (∀ x ∈ A, x.isSome) → (∀ x ∈ B, x.isSome) →
      A.map (Option.map Prod.fst) = B.map (Option.map Prod.fst) → A = B
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | a :: A, b :: B, hA, hB, sA, sB, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hab, hrest⟩ := h
    have ha := sA a (by simp)
    have hb := sB b (by simp)
    obtain ⟨⟨fa, da⟩, rfl⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨⟨fb, db⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
    simp only [Option.map_some, Option.some.injEq] at hab
    subst hab
    have hd : da = db :=
      VLCtx.key_unique hnd (hA (some (fa, da)) (by simp)) (hB (some (fa, db)) (by simp))
    subst hd
    congr 1
    exact VLCtx.keys_eq_of_fvars hnd (fun x hx => hA x (by simp [hx]))
      (fun x hx => hB x (by simp [hx])) (fun x hx => sA x (by simp [hx]))
      (fun x hx => sB x (by simp [hx])) hrest

theorem VLCtx.lams_of_declarations {fvs : List FVarId} {L : VLCtx}
    (H : List.Forall₂ (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), VLocalDecl.vlam type)) fvs L) :
    ∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d) := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · obtain ⟨deps, type, rfl⟩ := h
      exact ⟨_, _, rfl⟩
    · exact ih e he

theorem VLCtx.lams_of_cached {ps : List Expr} {L : VLCtx}
    (H : List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl ps L) :
    ∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d) := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · obtain ⟨fv, deps, type, _, rfl⟩ := h
      exact ⟨_, _, rfl⟩
    · exact ih e he

theorem VLCtx.fvars_drop_of_lams : ∀ {L : VLCtx} (m : Nat),
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      VLCtx.fvars (L.drop m) = L.fvars.drop m
  | [], m, _ => by simp
  | _ :: _, 0, _ => rfl
  | e :: L, m + 1, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp only [List.drop_succ_cons, VLCtx.fvars_cons_some]
    exact VLCtx.fvars_drop_of_lams m (fun x hx => h x (by simp [hx]))

theorem VLCtx.toCtx_length_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      L.toCtx.length = L.length
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.toCtx, VLCtx.toCtx_length_of_lams (L := L)
      (fun x hx => h x (by simp [hx]))]

theorem VLCtx.fvars_length_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      L.fvars.length = L.length
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.fvars_length_of_lams (L := L) (fun x hx => h x (by simp [hx]))]

theorem VLCtx.keys_fvars_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      (L.map Prod.fst).map (Option.map Prod.fst) = L.fvars.map some
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.keys_fvars_of_lams (L := L) (fun x hx => h x (by simp [hx]))]

theorem namedLambdaDeclarations_fvars
    {xs : List FVarId} {ys : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type)) xs ys) :
    VLCtx.fvars ys = xs := by
  induction H with
  | nil => rfl
  | cons hentry _ ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    simp [ih]

/-- Inverse of `TrExprS.abstractFVarLambdaSuffix`: the anonymous closure of a
named lambda suffix may be reopened with the same free variables. -/
theorem TrExprS.instantiateFVarLambdaSuffix {env : VEnv} {Us : List Name}
    {fvsRev : List FVarId} {scope : VLCtx}
    (Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), VLocalDecl.vlam type))
      fvsRev scope)
    (hnodup : fvsRev.Nodup) :
    ∀ {domains : List VExpr} {e : Expr} {e' : VExpr},
    TrExprS env Us
      (abstractForallContext ((VLCtx.toCtx scope).reverse ++ domains) [])
      (e.abstractList fvsRev.reverse domains.length) e' →
    TrExprS env Us (abstractForallContext domains scope) e e' := by
  induction Hdecls with
  | nil =>
    intro domains e e' Htr
    simpa [VLCtx.toCtx] using Htr
  | @cons fv entry fvsRev scope hentry Htail ih =>
    intro domains e e' Htr
    rcases hentry with ⟨deps, type, rfl⟩
    have hnodup' := List.nodup_cons.mp hnodup
    have hfv : fv ∉ fvsRev.reverse := by
      simpa using hnodup'.1
    have hsource :
        (e.abstract1 fv domains.length).abstractList fvsRev.reverse
            (type :: domains).length =
          e.abstractList (fv :: fvsRev).reverse domains.length := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := e) (a := fv) (as := fvsRev.reverse)
        (k := domains.length) hfv).symm
    have Htr' : TrExprS env Us
        (abstractForallContext ((VLCtx.toCtx scope).reverse ++ type :: domains) [])
        ((e.abstract1 fv domains.length).abstractList fvsRev.reverse
          (type :: domains).length) e' := by
      rw [hsource]
      simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using Htr
    have Hhead := ih hnodup'.2 Htr'
    have W := abstractForallContext.abstractHead domains scope fv deps type
    have hfresh : fv ∉ VLCtx.fvars scope := by
      rw [namedLambdaDeclarations_fvars Htail]
      exact hnodup'.1
    have Hinst := TrExprS.instantiateFVar W hfresh Hhead
    rwa [Expr.instantiate1'_abstract1_self] at Hinst

/-- Reopen the anonymous closure of a non-contiguous free-variable scope. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.instantiateAll
    {env : VEnv} {Us : List Name} {scope runtime : VLCtx}
    (H : checkInductiveTypes.loopType.ScopeEmbedding env Us scope runtime)
    (henv : env.WF) {source : Expr} {target : VExpr}
    (Htr : TrExprS env Us
      (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList scope.fvars.reverse) target) :
    TrExprS env Us scope source target := by
  have hnodup : scope.fvars.Nodup := (H.scopeWF henv).fvars_nodup
  have H' := TrExprS.instantiateFVarLambdaSuffix (domains := [])
    H.declarations hnodup (by simpa using Htr)
  simpa [abstractForallContext] using H'


theorem Expr.closed_mkAppList_fvars {f : Expr} (hf : Closed f) :
    ∀ (fvs : List FVarId), Closed (Expr.mkAppList f (fvs.map Expr.fvar))
  | [] => hf
  | fv :: fvs => by
    simp only [List.map_cons, Expr.mkAppList]
    exact Expr.closed_mkAppList_fvars (f := .app f (.fvar fv)) ⟨hf, trivial⟩ fvs

/-- The complete parameter/motive/minor scope of the recursor context, built
from the closed translation of the generated recursor type rather than by
restricting runtime translations. -/
theorem
    RecursorCheck.RuleAlignment.installedPrefixClosedScope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (k : Nat)
    (hup : IsFVarUpSet (· ∈ (H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars).take k) H.recursorWF.mlctx.vlctx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.ScopeEmbedding
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = (outerBinders.take k).reverse ∧
        Hscope.shift = fvarSelectionLift
          H.recursorWF.mlctx.vlctx.fvars (· ∈ outerBinders.take k) ∧
        (∀ body,
          Hscope.sourceTelescope.closeSource body =
            H.localContext.lctx.mkForall
              ((outerBinders.take k).map Expr.fvar).toArray body) ∧
        Closed (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
          (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
            (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
              H.recInfos[owner]!.major))) ∧
        ∃ t', Expr.ForallTelescopeTypeTranslation H.outVEnv Us scope
          (H.localContext.lctx.mkForall ((outerBinders.drop k).map Expr.fvar).toArray
            (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
              (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
                (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
                  H.recInfos[owner]!.major))))
          (outerBinders.length - k + (H.recInfos[owner]!.indices.size + 1)) t' := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases H.installedRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  have hrec : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let E := H.generated.entry owner howner
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have Hwf : H.recursorWF.mlctx.WF H.outVEnv Us :=
    H.recursorWF.mlctx_wf.mono hbase
  have hlctx : H.recursorWF.mlctx.lctx = H.localContext.lctx :=
    H.recursorWF.lctx_eq
  have hclosedL : LocalContext.LctxClosed H.localContext.lctx := by
    rw [← hlctx]
    exact Hwf.tr.lctxClosed
  -- every generated binder has a declaration
  have hmemDecl : ∀ fv, fv ∈ H.localContext.lctx.fvars →
      ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    rw [← hlctx] at hfv ⊢
    rw [Hwf.tr.fvars_eq] at hfv
    exact Hwf.tr.find?_eq_some.2 hfv
  -- the inner residual of the recursor type is closed
  let idxB := H.bindings.indices owner hrec
  let majB := H.bindings.major owner hrec
  have hall := H.noAlias
  have hidxNodup : idxB.fvars.Nodup := by
    have hsub1 : idxB.fvars <+ H.bindings.flatIndices.fvars := by
      apply List.sublist_flatten_of_mem
      simp only [List.mem_ofFn]
      exact ⟨⟨owner, hrec⟩, rfl⟩
    have hsub2 : H.bindings.flatIndices.fvars <+ RecInfoBindings.allFvars stats.params H.recInfos := by
      unfold RecInfoBindings.allFvars
      rw [H.bindings.flatIndices.exprArrayFVarIds]
      exact (List.sublist_append_left _ _).trans <|
        (List.sublist_append_right _ _).trans <|
        (List.sublist_append_right _ _).trans
          (List.sublist_append_right _ _)
    exact (hsub1.trans hsub2).nodup hall
  have hmajNodup : majB.fvars.Nodup := by
    have hlen := majB.length_fvars
    match h : majB.fvars, hlen with
    | [_], _ => simp
  have hbodyClosed : Closed (Expr.app
      (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major) := by
    rcases H.bindings.motives.getElem_eq_fvar owner (by simpa using hrec) with
      ⟨hmlt, hmotive⟩
    rcases majB.getElem_eq_fvar 0 (by simp) with ⟨hmjlt, hmajor⟩
    have hmot : H.recInfos[owner]!.motive =
        .fvar (H.bindings.motives.fvars[owner]'hmlt) := by
      simpa [getElem!_pos H.recInfos owner hrec] using hmotive
    have hmaj : H.recInfos[owner]!.major = .fvar (majB.fvars[0]'hmjlt) := by
      simpa using hmajor
    refine ⟨?_, by rw [hmaj]; trivial⟩
    rw [hmot, Expr.mkAppN_eq_mkAppList, idxB.expressions]
    simpa using Expr.closed_mkAppList_fvars
      (f := .fvar (H.bindings.motives.fvars[owner]'hmlt)) trivial idxB.fvars
  have hidxDecl : ∀ fv ∈ idxB.fvars, ∃ d, H.localContext.lctx.find? fv = some d :=
    fun fv hfv => hmemDecl fv (idxB.members fv hfv)
  have hmajDecl : ∀ fv ∈ majB.fvars, ∃ d, H.localContext.lctx.find? fv = some d :=
    fun fv hfv => hmemDecl fv (majB.members fv hfv)
  have hinnerClosed : Closed (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major)) := by
    rw [majB.expressions, LocalContext.mkForall]
    exact LocalContext.mkBinding_closed hmajDecl hmajNodup hbodyClosed
      hclosedL.declsClosed
  have hBClosed : Closed (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
          H.recInfos[owner]!.major))) := by
    have h := LocalContext.mkBinding_closed (isLambda := false)
      hidxDecl hidxNodup hinnerClosed hclosedL.declsClosed
    have key : ∀ (xs : Array Expr) (fvs : List FVarId) (inner : Expr),
        xs = (fvs.map Expr.fvar).toArray →
        Closed (H.localContext.lctx.mkForall ⟨fvs.map Expr.fvar⟩ inner) →
        Closed (H.localContext.lctx.mkForall xs inner) := by
      intro xs fvs inner h hc
      subst h
      exact hc
    exact key _ _ _ idxB.expressions h
  -- the generated recursor type, as one forall over the outer binders
  have houterNodup : outerBinders.Nodup := H.bindings.outerNodup H.params H.noAlias
  have houterDecl : ∀ fv ∈ outerBinders, ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    apply hmemDecl
    have hmem : fv ∈ H.recursorWF.mlctx.vlctx.fvars :=
      H.outerOrder.subset (List.mem_reverse.mpr hfv)
    rw [← hlctx, Hwf.tr.fvars_eq]
    exact hmem
  have HT := T.typed
  rw [E.type] at HT
  have HT' := Expr.ForallTelescopeTypeTranslation.of_inferImplicit 1000 false HT
  have hcount : stats.params.size + (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size + 1 =
      outerBinders.length + (H.recInfos[owner]!.indices.size + 1) := by
    simp only [outerBinders, List.length_append, H.params.length_fvars,
      H.bindings.motives.length_fvars, H.bindings.flatMinors.length_fvars]
    omega
  rw [hcount] at HT'
  rw [H.params.expressions, H.bindings.motives.expressions,
    H.bindings.flatMinors.expressions] at HT'
  let Bexpr := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major))
  have hMN : ∀ fv ∈ H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars,
      ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    apply houterDecl
    simp only [outerBinders, List.mem_append] at hfv ⊢
    rcases hfv with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hMNnd : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars).Nodup := by
    have h := houterNodup
    simp only [outerBinders, List.append_assoc] at h
    exact (List.nodup_append.mp h).2.1
  have hmm := LocalContext.mkForall_mkForall (lctx := H.localContext.lctx)
    (xs := H.bindings.motives.fvars) (ys := H.bindings.flatMinors.fvars)
    (b := Bexpr) hMN hMNnd hBClosed hclosedL
  rw [hmm] at HT'
  have hpm := LocalContext.mkForall_mkForall (lctx := H.localContext.lctx)
    (xs := H.params.fvars)
    (ys := H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars)
    (b := Bexpr)
    (fun fv hfv => houterDecl fv (by
      simpa [outerBinders, List.append_assoc] using hfv))
    (by simpa [outerBinders, List.append_assoc] using houterNodup)
    hBClosed hclosedL
  rw [hpm, ← List.append_assoc] at HT'
  rw [← hlctx] at HT'
  -- split the outer binders at the selected prefix
  have hsplitL : outerBinders = outerBinders.take k ++ outerBinders.drop k :=
    (List.take_append_drop k outerBinders).symm
  have hdropNodup : (outerBinders.drop k).Nodup :=
    (List.drop_sublist k outerBinders).nodup houterNodup
  have hdropDecl : ∀ fv ∈ outerBinders.drop k,
      ∃ d, H.localContext.lctx.find? fv = some d :=
    fun fv hfv => houterDecl fv (List.mem_of_mem_drop hfv)
  have hrestClosed : Closed (H.localContext.lctx.mkForall
      ((outerBinders.drop k).map Expr.fvar).toArray Bexpr) := by
    rw [LocalContext.mkForall]
    exact LocalContext.mkBinding_closed hdropDecl hdropNodup hBClosed
      hclosedL.declsClosed
  have htd := LocalContext.mkForall_mkForall (lctx := H.localContext.lctx)
    (xs := outerBinders.take k) (ys := outerBinders.drop k) (b := Bexpr)
    (fun fv hfv => houterDecl fv (by rw [← hsplitL] at hfv; exact hfv))
    (by rw [← hsplitL]; exact houterNodup) hBClosed hclosedL
  rw [← hsplitL] at htd
  rw [← hlctx] at htd
  rw [← htd] at HT'
  have hselNodup : (outerBinders.take k).Nodup :=
    (List.take_sublist k outerBinders).nodup houterNodup
  have hselDecl : ∀ fv ∈ outerBinders.take k,
      ∃ d, H.recursorWF.mlctx.lctx.find? fv = some d := by
    intro fv hfv
    rw [hlctx]
    exact houterDecl fv (List.mem_of_mem_take hfv)
  have hfilter : H.recursorWF.mlctx.vlctx.fvars.filter
      (· ∈ outerBinders.take k) = (outerBinders.take k).reverse := by
    have hsub : (outerBinders.take k).reverse <+ H.recursorWF.mlctx.vlctx.fvars :=
      ((List.take_sublist k outerBinders).reverse).trans H.outerOrder
    have h := checkInductiveTypes.loopType.List.filter_mem_eq_of_sublist_nodup hsub
      Hwf.tr.wf.fvars_nodup
    rw [← h]
    apply List.filter_congr
    intro fv _
    simp
  have hcountK : outerBinders.length + (H.recInfos[owner]!.indices.size + 1) =
      (outerBinders.take k).length +
        (outerBinders.length - k + (H.recInfos[owner]!.indices.size + 1)) := by
    simp only [List.length_take]
    omega
  rw [hcountK] at HT'
  obtain ⟨scope, Hscope, hscope, hshift, hclose, t', HE, _⟩ :=
    MLCtxOnlyLams.closedTelescopeScope H.recursorWF.onlyLams H.outVEnvWF Hwf
      (outerBinders.take k) _ _ hselDecl hselNodup
      (by rw [hlctx]; exact hrestClosed) hfilter hup HT'
  refine ⟨scope, Hscope, hscope, hshift, ?_, hBClosed, t', ?_⟩
  · intro body
    rw [hclose body, hlctx]
  · rw [hlctx] at HE
    exact HE

/-- Close the exact selected-minor declaration through the independently
dependency-selected free-variable scope.  This exposes two translations of the same
closed source domain: one over the scope's semantic domains and one over the
generated recursor telescope.  Their context comparison is the remaining
step needed by the canonical RHS application. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorExactClosedDomain
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ D : FVarDeclAt H.localContext
          (H.recInfos.flatMap (·.minors)) minorIdx,
      ∃ _O : H.origins.FlatMinorBinderType D,
      ∃ _S : MinorPremiseType,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.ScopeEmbedding
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowTarget,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sourceTelescope.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        TrExprS H.outVEnv Us scope D.type narrowTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext scope.toCtx.reverse [])
          (D.type.abstractList sourceBinders) narrowTarget ∧
        OnCtx (abstractForallContext scope.toCtx.reverse []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
          T.minors[minorIdx]! := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.installedSelectedMinorDomain with
    ⟨T, D, O, S, Hdomain, HdomainType⟩
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  have hminorLt : minorIdx < H.bindings.flatMinors.fvars.length := by
    rw [H.bindings.flatMinors.length_fvars]
    exact D.inBounds
  let k := H.params.fvars.length + H.bindings.motives.fvars.length + minorIdx
  have hk : k ≤ outerBinders.length := by
    simp only [k, outerBinders, List.length_append]
    omega
  have htake : outerBinders.take k = sourceBinders := by
    simp only [k, outerBinders, sourceBinders, List.append_assoc]
    rw [Nat.add_assoc, List.take_length_add_append, List.take_length_add_append]
  have hminorFv : H.bindings.flatMinors.fvars[minorIdx]'hminorLt = D.fvar := by
    rcases H.bindings.flatMinors.getElem_eq_fvar minorIdx D.inBounds with
      ⟨_, hget⟩
    have h := D.expression
    rw [hget] at h
    exact Expr.fvar.inj h
  have hdropEq : outerBinders.drop k =
      D.fvar :: H.bindings.flatMinors.fvars.drop (minorIdx + 1) := by
    simp only [k, outerBinders, List.append_assoc]
    rw [Nat.add_assoc, List.drop_length_add_append, List.drop_length_add_append,
      List.drop_eq_getElem_cons hminorLt, hminorFv]
  have hup := A.installedSelectedMinorPrefixUp
  obtain ⟨scope, Hscope, hscope, hscopeShift, hscopeSource, hBClosed, t', HE⟩ :=
    RecursorCheck.RuleAlignment.installedPrefixClosedScope
      (H := H) (owner := owner) (howner := howner) k (by rw [htake]; exact hup)
  rw [htake] at hscope hscopeShift hscopeSource
  rw [hdropEq] at HE
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hclosedL : LocalContext.LctxClosed H.localContext.lctx := by
    rw [← H.recursorWF.lctx_eq]
    exact (H.recursorWF.mlctx_wf.mono hbase).tr.lctxClosed
  have hrestDecl : ∀ fv ∈ H.bindings.flatMinors.fvars.drop (minorIdx + 1),
      ∃ d, H.localContext.lctx.find? fv = some d := by
    intro fv hfv
    have hmem : fv ∈ H.recursorWF.mlctx.vlctx.fvars := by
      apply H.outerOrder.subset
      apply List.mem_reverse.mpr
      exact List.mem_append_right _ (List.mem_of_mem_drop hfv)
    rw [← H.recursorWF.lctx_eq]
    exact H.recursorWF.mlctx_wf.tr.find?_eq_some.2 hmem
  have hconsNodup : (D.fvar :: H.bindings.flatMinors.fvars.drop (minorIdx + 1)).Nodup := by
    rw [← hdropEq]
    exact (List.drop_sublist k outerBinders).nodup
      (H.bindings.outerNodup H.params H.noAlias)
  rw [LocalContext.mkForall_cons_cdecl D.declaration hrestDecl hconsNodup hBClosed
    hclosedL] at HE
  have hcount : outerBinders.length - k + (H.recInfos[owner]!.indices.size + 1) =
      (outerBinders.length - k - 1 + (H.recInfos[owner]!.indices.size + 1)) + 1 := by
    have : k < outerBinders.length := by
      simp only [k, outerBinders, List.length_append]
      omega
    omega
  rw [hcount] at HE
  cases HE with
  | cons Hnarrow _ _ =>
  have Hclosed := Hscope.abstractAll H.outVEnvWF Hnarrow
  rw [hscope, List.reverse_reverse] at Hclosed
  exact ⟨T, D, O, S, scope, Hscope, _, hscope,
    hscopeShift, hscopeSource, Hnarrow, Hclosed,
    Hscope.abstractAllWF H.outVEnvWF, Hdomain, HdomainType⟩

/-- Reconstruct the complete source telescope of the exact selected prefix.
Its abstract domains are precisely the non-contiguous dependency-selected context and
its arity is precisely the generated parameter/motive/earlier-minor prefix.
This is the binder-by-binder comparison input missing from the earlier
whole-domain closing theorem. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorExactPrefixSource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.ScopeEmbedding
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ prefixSource,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sourceTelescope.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        prefixSource = Hscope.sourceTelescope.closeSource
          (.sort (.zero : Level)) ∧
        prefixSource = H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level)) ∧
        TrExprS H.outVEnv Us [] prefixSource
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        H.outVEnv.IsType Us.length []
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us [] prefixSource
          scope.length
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        scope.toCtx.reverse.length =
          (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.installedSelectedMinorExactClosedDomain with
    ⟨T, _D, _O, _S, scope, Hscope, _narrowTarget, hscope,
      hscopeShift, hscopeSource, _Hnarrow, _Hclosed, _HscopeWF,
      _Hdomain, _HdomainType⟩
  rcases Hscope.closedSortTranslation H.outVEnvWF with
    ⟨Hprefix, HprefixType⟩
  have HprefixTelescope := Hscope.closedSortTelescope H.outVEnvWF
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hprefixLength : scope.toCtx.reverse.length =
      (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
    calc
      scope.toCtx.reverse.length = scope.length := by
        simpa using Hscope.toCtx_length
      _ = scope.fvars.length := Hscope.fvars_length.symm
      _ = sourceBinders.reverse.length := congrArg List.length hscope
      _ = sourceBinders.length := by simp
      _ = (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
        simp only [sourceBinders, List.length_append, List.length_take]
        rw [H.params.length_fvars, H.bindings.motives.length_fvars,
          H.bindings.flatMinors.length_fvars,
          T.params_length, T.motives_length, T.minors_length]
  exact ⟨T, scope, Hscope,
    Hscope.sourceTelescope.closeSource (.sort (.zero : Level)), hscope,
    hscopeShift, hscopeSource, rfl,
    hscopeSource (.sort (.zero : Level)),
    Hprefix, HprefixType, HprefixTelescope, hprefixLength⟩

/-- A concrete parameter/motive/minor prefix and the executable recursor have
the same source domain at every retained slot.  The proof selects the exact
local declaration on both sides, rather than appealing to whole-expression
equality. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorPrefixBinderEq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (minorLimit : Nat)
    (hminorLimit : minorLimit ≤ H.bindings.flatMinors.fvars.length) :
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorLimit
    ∀ position (_hposition : position < sourceBinders.length)
      {prefixDomain recursorDomain : Expr},
      Expr.ForallBinderAt
        (H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level))) position prefixDomain →
      Expr.ForallBinderAt
        (H.generated.entry owner howner).info.type position recursorDomain →
      prefixDomain = recursorDomain := by
  dsimp only
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorLimit
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have hsourceNodup : sourceBinders.Nodup := by
    have houter := H.bindings.outerNodup H.params H.noAlias
    have hsub :
        (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars.take minorLimit <+
          (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars :=
      (List.Sublist.refl
        (H.params.fvars ++ H.bindings.motives.fvars)).append
          (List.take_sublist _ H.bindings.flatMinors.fvars)
    simpa [sourceBinders, List.append_assoc] using houter.sublist hsub
  have hsourceMembers : ∀ fv ∈ sourceBinders,
      fv ∈ H.localContext.lctx.fvars := by
    intro fv hfv
    rcases List.mem_append.mp hfv with hprefix | hminor
    · rcases List.mem_append.mp hprefix with hparam | hmotive
      · exact H.params.members fv hparam
      · exact H.bindings.motives.members fv hmotive
    · exact H.bindings.flatMinors.members fv
        (List.mem_of_mem_take hminor)
  have hsourceDecls : ∀ fv ∈ sourceBinders,
      ∃ index name type bi kind,
        H.localContext.lctx.find? fv =
          some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    exact H.localWF.findCDecl fv (hsourceMembers fv hfv)
  intro position hposition prefixDomain recursorDomain Hprefix Hrecursor
  by_cases hparam : position < H.params.fvars.length
  · have hparamArray : position < stats.params.size := by
      rw [← H.params.length_fvars]
      exact hparam
    rcases H.params.declarationAt H.localWF position hparamArray with ⟨D⟩
    rcases H.params.getElem_eq_fvar position hparamArray with
      ⟨_hparamFVars, hparamExpr⟩
    have hparamFVar : H.params.fvars[position] = D.fvar :=
      Expr.fvar.inj (hparamExpr.symm.trans D.expression)
    have hsourceAt : sourceBinders[position] = D.fvar := by
      rw [List.getElem_append_left]
      · rw [List.getElem_append_left hparam]
        exact hparamFVar
      · simp only [List.length_append]
        omega
    have htake : sourceBinders.take position =
        H.params.fvars.take position := by
      dsimp only [sourceBinders]
      rw [List.take_append, List.take_append]
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hparam)]
      rw [Nat.sub_eq_zero_of_le (by simp; omega :
        position ≤ (H.params.fvars ++ H.bindings.motives.fvars).length)]
      simp
    have HprefixCanonical :=
      LocalContext.mkForall_fvars_forallBinderAtList hsourceDecls hsourceNodup
        position hposition D.index D.userName D.type D.binderInfo D.kind (by
          rw [hsourceAt]
          exact D.declaration)
        (D.closed H.recursorWF.lctxClosed)
        (body := (.sort (.zero : Level)))
    have HrecursorCanonical :=
      selections.parameterBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
    dsimp only at HrecursorCanonical
    rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
    have hprefixDomain : prefixDomain =
        D.type.abstractList (H.params.fvars.take position) := by
      rw [← htake]
      exact Hprefix.unique HprefixCanonical
    exact hprefixDomain.trans
      (Hrecursor.unique HrecursorCanonical).symm
  · by_cases hmotive : position <
        H.params.fvars.length + H.bindings.motives.fvars.length
    · let motivePos := position - H.params.fvars.length
      have hmotivePos : motivePos < H.bindings.motives.fvars.length := by
        dsimp only [motivePos]
        omega
      have hmotiveArray : motivePos <
          (H.recInfos.map (·.motive)).size := by
        rw [← H.bindings.motives.length_fvars]
        exact hmotivePos
      rcases H.bindings.motives.declarationAt H.localWF motivePos
          hmotiveArray with ⟨D⟩
      rcases H.bindings.motives.getElem_eq_fvar motivePos hmotiveArray with
        ⟨_hmotiveFVars, hmotiveExpr⟩
      have hmotiveFVar : H.bindings.motives.fvars[motivePos] = D.fvar :=
        Expr.fvar.inj (hmotiveExpr.symm.trans D.expression)
      have hpositionEq : H.params.fvars.length + motivePos = position := by
        dsimp only [motivePos]
        omega
      have hsourceAt : sourceBinders[position] = D.fvar := by
        rw [List.getElem_append_left]
        · rw [List.getElem_append_right (Nat.le_of_not_gt hparam)]
          simpa [motivePos] using hmotiveFVar
        · simp only [List.length_append]
          omega
      have htake : sourceBinders.take position =
          H.params.fvars ++
            H.bindings.motives.fvars.take motivePos := by
        rw [← hpositionEq]
        dsimp only [sourceBinders]
        rw [List.take_append, List.take_append]
        rw [List.take_of_length_le (by omega :
          H.params.fvars.length ≤ H.params.fvars.length + motivePos)]
        rw [Nat.sub_eq_zero_of_le (by simp; omega :
          H.params.fvars.length + motivePos ≤
            (H.params.fvars ++ H.bindings.motives.fvars).length)]
        simp
      have HprefixCanonical :=
        LocalContext.mkForall_fvars_forallBinderAtList hsourceDecls hsourceNodup
          position hposition D.index D.userName D.type D.binderInfo D.kind (by
            rw [hsourceAt]
            exact D.declaration)
        (D.closed H.recursorWF.lctxClosed)
          (body := (.sort (.zero : Level)))
      have HrecursorCanonical :=
        selections.motiveBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
      dsimp only at HrecursorCanonical
      rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
      have hstatsPosition : stats.params.size + motivePos = position := by
        rw [← H.params.length_fvars]
        exact hpositionEq
      rw [hstatsPosition] at HrecursorCanonical
      have hprefixDomain : prefixDomain = D.type.abstractList
          (H.params.fvars ++
            H.bindings.motives.fvars.take motivePos) := by
        rw [← htake]
        exact Hprefix.unique HprefixCanonical
      exact hprefixDomain.trans
        (Hrecursor.unique HrecursorCanonical).symm
    · let priorPos := position -
        (H.params.fvars.length + H.bindings.motives.fvars.length)
      have hpriorPos : priorPos < minorLimit := by
        dsimp only [priorPos, sourceBinders] at hposition ⊢
        simp only [List.length_append, List.length_take,
          Nat.min_eq_left hminorLimit] at hposition
        omega
      have hpriorArray : priorPos <
          (H.recInfos.flatMap (·.minors)).size := by
        rw [← H.bindings.flatMinors.length_fvars]
        exact Nat.lt_of_lt_of_le hpriorPos hminorLimit
      rcases H.bindings.flatMinors.declarationAt H.localWF priorPos
          hpriorArray with ⟨D⟩
      rcases H.bindings.flatMinors.getElem_eq_fvar priorPos hpriorArray with
        ⟨_hpriorFVars, hpriorExpr⟩
      have hpriorFVar : H.bindings.flatMinors.fvars[priorPos] = D.fvar :=
        Expr.fvar.inj (hpriorExpr.symm.trans D.expression)
      have hpositionEq : H.params.fvars.length +
          H.bindings.motives.fvars.length + priorPos = position := by
        dsimp only [priorPos]
        omega
      have hsourceAt : sourceBinders[position] = D.fvar := by
        rw [List.getElem_append_right (by
          simp only [List.length_append]
          omega : (H.params.fvars ++ H.bindings.motives.fvars).length ≤
            position)]
        rw [List.getElem_take]
        simpa only [List.length_append, priorPos] using hpriorFVar
      have htake : sourceBinders.take position =
          H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take priorPos := by
        rw [← hpositionEq]
        dsimp only [sourceBinders]
        rw [List.take_append, List.take_append]
        rw [List.take_of_length_le (by omega :
          H.params.fvars.length ≤ H.params.fvars.length +
            H.bindings.motives.fvars.length + priorPos)]
        have hmotivesCount :
            H.params.fvars.length + H.bindings.motives.fvars.length +
                priorPos - H.params.fvars.length =
              H.bindings.motives.fvars.length + priorPos := by omega
        rw [hmotivesCount, List.take_of_length_le (by omega)]
        have hminorCount :
            H.params.fvars.length + H.bindings.motives.fvars.length +
                priorPos -
                  (H.params.fvars ++ H.bindings.motives.fvars).length =
              priorPos := by
          simp only [List.length_append]
          omega
        rw [hminorCount, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt hpriorPos)]
      have HprefixCanonical :=
        LocalContext.mkForall_fvars_forallBinderAtList hsourceDecls hsourceNodup
          position hposition D.index D.userName D.type D.binderInfo D.kind (by
            rw [hsourceAt]
            exact D.declaration)
        (D.closed H.recursorWF.lctxClosed)
          (body := (.sort (.zero : Level)))
      have HrecursorCanonical :=
        selections.minorBinderAtList hselectionNoAlias H.recursorWF.lctxClosed D
      dsimp only at HrecursorCanonical
      rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
      have hstatsPosition : stats.params.size +
          (H.recInfos.map (·.motive)).size + priorPos = position := by
        rw [← H.params.length_fvars,
          ← H.bindings.motives.length_fvars]
        exact hpositionEq
      rw [hstatsPosition] at HrecursorCanonical
      have hprefixDomain : prefixDomain = D.type.abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take priorPos) := by
        rw [← htake]
        exact Hprefix.unique HprefixCanonical
      exact hprefixDomain.trans
        (Hrecursor.unique HrecursorCanonical).symm

/-- The independently dependency-selected selected-minor source prefix and the
executable recursor have the same domain at every retained parameter,
motive, and earlier-minor slot. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorPrefixBinderEq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ position (_hposition : position < sourceBinders.length)
      {prefixDomain recursorDomain : Expr},
      Expr.ForallBinderAt
        (H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level))) position prefixDomain →
      Expr.ForallBinderAt
        (H.generated.entry owner howner).info.type position recursorDomain →
      prefixDomain = recursorDomain := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  apply RecursorCheck.RuleAlignment.installedMinorPrefixBinderEq (H := H) minorIdx
  rw [H.bindings.flatMinors.length_fvars]
  exact Nat.le_of_lt A.rule.minor_valid

/-- The exact semantic context retained by non-contiguous dependency selection is
definitionally equal to the generated recursor's parameter/motive/earlier-
minor prefix.  This closes the dependent outer-context conversion needed to
type the canonical rule right-hand side. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorPrefixDefEqCtx
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.ScopeEmbedding
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sourceTelescope.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.installedSelectedMinorExactPrefixSource with
    ⟨T, scope, Hscope, prefixSource, hscope, hscopeShift, hscopeSource,
      hprefixSource, hprefixLocal, _HprefixTr, _HprefixType, HprefixTelescope,
      hselectedLength⟩
  let fullDomains := T.params ++ T.motives ++ T.minors ++
    T.indices ++ T.major
  let selectedDomains := T.params ++ T.motives ++ T.minors.take minorIdx
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hscopeDomainsLength : scope.toCtx.reverse.length = scope.length := by
    simpa using Hscope.toCtx_length
  have hfullLength : fullDomains.length =
      stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size +
          H.recInfos[owner]!.indices.size + 1 := by
    simp only [fullDomains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length, T.major_length]
  have hselectedArity : selectedDomains.length = sourceBinders.length := by
    simp only [selectedDomains, sourceBinders, List.length_append,
      List.length_take]
    rw [H.params.length_fvars, H.bindings.motives.length_fvars,
      H.bindings.flatMinors.length_fvars,
      T.params_length, T.motives_length, T.minors_length]
  have hscopeArity : sourceBinders.length = scope.length := by
    calc
      sourceBinders.length = sourceBinders.reverse.length := by simp
      _ = scope.fvars.length := congrArg List.length hscope.symm
      _ = scope.length := Hscope.fvars_length
  have Hctx := HprefixTelescope.commonPrefixDefEqCtx H.outVEnvWF T.typed
    scope.toCtx.reverse fullDomains (.sort (.zero : VLevel)) T.result
    rfl
    (by simpa [fullDomains, List.append_assoc] using T.target_eq)
    hscopeDomainsLength hfullLength sourceBinders.length
    (Nat.le_of_eq hscopeArity) (by
      have hselectedLeFull : selectedDomains.length ≤ fullDomains.length := by
        have htakeLe := List.length_take_le minorIdx T.minors
        simp only [selectedDomains, fullDomains, List.length_append] at ⊢
        omega
      calc
        sourceBinders.length = selectedDomains.length := hselectedArity.symm
        _ ≤ fullDomains.length := hselectedLeFull
        _ = stats.params.size + (H.recInfos.map (·.motive)).size +
            (H.recInfos.flatMap (·.minors)).size +
              H.recInfos[owner]!.indices.size + 1 := hfullLength) (by
        intro position hposition _hiPrefix _hiRecursor
          prefixDomain recursorDomain HprefixBinder HrecursorBinder
        apply A.installedSelectedMinorPrefixBinderEq position hposition
        · rw [← hprefixLocal]
          exact HprefixBinder
        · exact HrecursorBinder)
  have htakeScope : (scope.toCtx.reverse).take sourceBinders.length =
      scope.toCtx.reverse := by
    rw [hscopeArity, ← hscopeDomainsLength]
    exact List.take_length
  have htakeFull : fullDomains.take sourceBinders.length =
      selectedDomains := by
    rw [← hselectedArity]
    rw [show fullDomains =
        selectedDomains ++
          (T.minors.drop minorIdx ++ T.indices ++ T.major) by
      have hsplit := (List.take_append_drop minorIdx T.minors).symm
      simpa only [fullDomains, selectedDomains, List.append_assoc] using
        congrArg (fun minors =>
          T.params ++ T.motives ++ minors ++ T.indices ++ T.major) hsplit]
    exact List.take_append_length
  rw [htakeScope, htakeFull] at Hctx
  exact ⟨T, scope, Hscope, hscope, hscopeShift, hscopeSource, by
    simpa [selectedDomains, List.reverse_append, List.append_assoc] using
      Hctx⟩

/-- Invert the flattened minor lookup at this rule's canonical offset.  The
row owner and row-local slot recovered from the retained declaration are the
same owner/constructor coordinates used by the rule traversal. -/
theorem
    RecursorCheck.RuleAlignment.selectedMinorOriginPosition
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {D : FVarDeclAt H.localContext
      (H.recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes owner + i)}
    (O : H.origins.FlatMinorBinderType D) :
    O.owner = owner ∧ O.localIndex = i := by
  let minorIdx := recursorMinorOffset indTypes owner + i
  let originIdx := recursorMinorOffset indTypes O.owner + O.localIndex
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have horiginOwner : O.owner < indTypes.size := by
    rw [← hsizes]
    exact O.owner_lt
  have horiginLocal : O.localIndex < indTypes[O.owner]!.ctors.length := by
    rw [← H.minorCounts O.owner O.owner_lt]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  have horiginRoom := recursorMinorOffset_room indTypes O.owner horiginOwner
  have hflatSize : (H.recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size :=
    mkRecInfos.flatMinors_size hsizes H.minorCounts
  have horiginIdx : originIdx <
      (H.recInfos.flatMap (·.minors)).size := by
    have hconcrete : originIdx <
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      dsimp only [originIdx]
      omega
    rw [hflatSize, ← ownedConstructors_length_eq_flattened_size]
    simpa [ownedConstructors, List.length_flatMap] using hconcrete
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have hflatNodup :
      (H.recInfos.flatMap (·.minors)).toList.Nodup := by
    rw [H.bindings.flatMinors.expressions]
    have mapFVarNodup : ∀ xs : List FVarId, xs.Nodup →
        (xs.map Expr.fvar).Nodup := by
      intro xs hxs
      induction hxs with
      | nil => exact .nil
      | @cons fv xs hnotmem _ ih =>
          exact .cons (by simpa using hnotmem) ih
    have hminorNodup : H.bindings.flatMinors.fvars.Nodup := by
      simpa [selections, RecInfoBindings.toRecursorBinderGroups,
        FVarArrayIn.toCDeclArray] using hnoalias.parts.minors
    exact mapFVarNodup _ hminorNodup
  have htoListFlatMap :
      (H.recInfos.flatMap (·.minors)).toList =
        H.recInfos.toList.flatMap (fun info => info.minors.toList) := by
    exact Array.toList_flatMap
  have horiginIdxRows : originIdx <
      (H.recInfos.toList.flatMap
        (fun info => info.minors.toList)).length := by
    rw [← htoListFlatMap, Array.length_toList]
    exact horiginIdx
  have horiginIdxList : originIdx <
      (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]
    exact horiginIdx
  have hminorIdxList : minorIdx <
      (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]
    simpa [minorIdx] using D.inBounds
  have horiginLocalList : O.localIndex <
      H.recInfos[O.owner].minors.toList.length := by
    simpa using O.local_lt
  have HoriginGet := List.flatMap_getElem_prefix H.recInfos.toList
    (fun info => info.minors.toList) O.owner O.localIndex
    (by simpa using O.owner_lt)
    (by simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt)
    (by
      rw [H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)]
      simpa [originIdx] using horiginIdxRows)
  have HoriginGet' :
      (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
        H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList := by
    simpa [Array.toList_flatMap, originIdx,
      H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)] using
      HoriginGet
  have hvalue :
      (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
        (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
    calc
      _ = H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList :=
        HoriginGet'
      _ = (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
        simpa only [Array.getElem_toList] using O.expression_eq
  have hposition : originIdx = minorIdx :=
    (List.getElem_inj (h₀ := horiginIdxList)
      (h₁ := hminorIdxList) hflatNodup).mp hvalue
  have hownerEq : O.owner = owner := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hmono := recursorMinorOffset_mono indTypes (O.owner + 1)
          owner (by omega) (by omega)
      have hstep := recursorMinorOffset_step indTypes O.owner horiginOwner
      dsimp only [originIdx, minorIdx] at hposition
      rw [hstep] at hmono
      omega
    · have hownerSource : owner < indTypes.size := by omega
      have hmono := recursorMinorOffset_mono indTypes (owner + 1)
          O.owner (by omega) (by omega)
      have hstep := recursorMinorOffset_step indTypes owner hownerSource
      dsimp only [originIdx, minorIdx] at hposition
      rw [hstep] at hmono
      omega
  refine ⟨hownerEq, ?_⟩
  dsimp only [originIdx, minorIdx] at hposition
  rw [hownerEq] at hposition
  omega

end VerifyInductive
end Lean4Lean
