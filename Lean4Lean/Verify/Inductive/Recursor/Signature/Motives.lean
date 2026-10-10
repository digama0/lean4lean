import Lean4Lean.Verify.Inductive.Recursor.Signature.IndexDomains
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem TrExprS.forallPrefixContextEq
    (henv : env.WF) (Htel : Expr.ForallTelescope source n residual)
    (hlen₁ : domains₁.length = n) (hlen₂ : domains₂.length = n)
    (Htr₁ : TrExprS env Us Δ₁ source (VExpr.wrapForalls domains₁ result₁))
    (Htr₂ : TrExprS env Us Δ₂ source (VExpr.wrapForalls domains₂ result₂))
    (Hctx : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) :
    VLCtx.IsDefEq env Us.length (abstractForallContext domains₁ Δ₁)
      (abstractForallContext domains₂ Δ₂) := by
  induction Htel generalizing Δ₁ Δ₂ domains₁ domains₂ result₁ result₂ with
  | nil =>
    have hnil₁ := List.eq_nil_of_length_eq_zero hlen₁
    have hnil₂ := List.eq_nil_of_length_eq_zero hlen₂
    subst domains₁ domains₂
    simpa [abstractForallContext] using Hctx
  | cons Htel ih =>
    cases domains₁ with
    | nil => simp at hlen₁
    | cons dom₁ domains₁ =>
      cases domains₂ with
      | nil => simp at hlen₂
      | cons dom₂ domains₂ =>
        cases Htr₁ with
        | forallE HdomType₁ _ Hdom₁ Hbody₁ =>
          cases Htr₂ with
          | forallE _ _ Hdom₂ Hbody₂ =>
            have Heq := Hdom₁.uniq henv Hctx Hdom₂
            have Hnext : VLCtx.IsDefEq env Us.length
                ((none, .vlam dom₁) :: Δ₁) ((none, .vlam dom₂) :: Δ₂) :=
              .cons Hctx nofun (.vlam (Heq.of_l henv Hctx.wf.toCtx HdomType₁.choose_spec))
            simpa [abstractForallContext, List.map_append, List.append_assoc] using
              ih (by simpa using hlen₁) (by simpa using hlen₂) Hbody₁ Hbody₂ Hnext

theorem TrExprS.forallTelescope_residual_typed
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (Htype : env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result)) :
    TrExprS env Us (abstractForallContext domains Δ) residual result ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx result := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Htr Htype
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htr with
      | forallE _ HbodyType _ Hbody =>
        simpa [abstractForallContext, List.map_append, List.append_assoc] using
          ih (by simpa using hlen) Hbody HbodyType

/-- If the first `n` domains of `source` (closed with `Prop`, `Expr.forallDomainsOnly`)
translate to `domains`, and the residual after them translates to a type `result` in the
context extended by `domains`, then `source` translates to `wrapForalls domains result`, which
is a type. -/
theorem TrExprS.rebuildForallPrefix
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Htemplate : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls domains (.sort .zero)))
    (Hres : TrExprS env Us (abstractForallContext domains Δ) residual result)
    (HresType : env.IsType Us.length (abstractForallContext domains Δ).toCtx result) :
    TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Hres HresType
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htemplate with
      | forallE HdomType _ Hdom Hbody =>
        obtain ⟨Hbody', HbodyType⟩ := ih (by simpa using hlen) Hbody
          (by simpa [abstractForallContext, List.map_append, List.append_assoc] using Hres)
          (by simpa [abstractForallContext, List.map_append, List.append_assoc] using HresType)
        exact ⟨.forallE HdomType HbodyType Hdom Hbody', .forallE HdomType HbodyType⟩

/-- Given index domains `indices` that translate the executable index telescope of family
`owner` (`indexDomainSource`), the executable motive type (indices, major, elimination sort,
abstracted over the parameters) translates in the recursor-checking environment to
`∀ indices, (family applied to the bvar spine) → Sort level`, which is a type in the recursor
parameter context. Typehood of the major-and-sort residual comes from the executable's own
check, moved into the index context by conversion. -/
theorem RecursorConstruction.replayMotiveWithIndexDomains
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (hindices : indices.length = H.recInfos[owner]!.indices.size)
    (hlevels : stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)) = some levels)
    (hlevel : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some level)
    (Hindex : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      (H.indexDomainSource owner) (VExpr.wrapForalls indices (.sort .zero))) :
    let motive := VExpr.wrapForalls indices (.forallE
      (VExpr.mkApps (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        levels)
        (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))) (.sort level))
    TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars) motive ∧
      H.recursorWF.venv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx motive := by
  have henv := H.recursorWF.checking.tr.wf
  obtain ⟨S, oldIndices, oldMajor, oldLevel, holdIndices, _, Htr, Htype, _⟩ :=
    H.unannotatedMotiveDomains owner howner
  have Htel := (S.indicesBound.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
      H.params.fvars
  simp only [Nat.zero_add] at Htel
  have Hprefix := (TrExprS.forallDomainsOnly Htel holdIndices Htr).1
  have hbase : VLCtx.WF H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) := by
    have hp := H.parameterSuffix.parameterWF
    have hctx := abstractForallContext.isDefEq
      (left := H.parameterSuffix.parameterDecls.toCtx.reverse)
      (right := H.parameterSuffix.parameterDecls.toCtx.reverse)
      (by simpa using VEnv.IsDefEqCtx.refl hp.toCtx)
    exact hctx.wf
  have Hcontexts := TrExprS.forallPrefixContextEq henv Htel.domainsOnly
    holdIndices hindices Hprefix Hindex (.refl henv hbase)
  have Htype' : H.recursorWF.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []).toCtx
      (VExpr.wrapForalls oldIndices (.forallE oldMajor (.sort oldLevel))) := by
    simpa [VLCtx.toCtx] using Htype
  obtain ⟨Hres, HresType⟩ := TrExprS.forallTelescope_residual_typed Htel holdIndices Htr Htype'
  obtain ⟨newResult, HnewRes⟩ := Hres.defeqDFC henv Hcontexts
  have HresEq := Hres.uniq henv Hcontexts HnewRes
  have HnewType := (HresType.defeqU_l henv Hcontexts.wf.toCtx HresEq).defeqDFC
    henv.ordered Hcontexts.defeqCtx
  have HmajorTel := ((S.majorBound.mkForall_forallTelescope H.localWF (.sort H.elimLevel)).abstractN
    S.indicesBound.fvars).abstractList H.params.fvars H.recInfos[owner]!.indices.size
  have hsort (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractList fvars k = .sort H.elimLevel :=
    Expr.abstractList_eq_self_of_abstract1 (.sort H.elimLevel)
      (by intro fv depth; simp [Expr.abstract1]) fvars k
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractN fvars k = .sort H.elimLevel := rfl
  simp only [Array.size_singleton, hsort, hsortN] at HmajorTel
  obtain ⟨majorDomains, residual, hmajorLen, hnewResult, Hsort⟩ :=
    TrExprS.forallTelescope_shape_with_context HmajorTel HnewRes
  cases majorDomains with
  | nil => simp at hmajorLen
  | cons major majorTail =>
    have hnil : majorTail = [] := by simpa using hmajorLen
    subst majorTail
    cases Hsort with
    | sort hsortLevel =>
      rw [hlevel] at hsortLevel
      cases Option.some.inj hsortLevel
      simp only [VExpr.wrapForalls] at hnewResult
      rw [hnewResult] at HnewRes HnewType
      obtain ⟨Hfull, HfullType⟩ := TrExprS.rebuildForallPrefix Htel hindices Hindex HnewRes HnewType
      have HmajorEq := H.unannotatedMotiveMajor owner howner hindices hlevels Hfull
      rw [HmajorEq] at Hfull HfullType
      exact ⟨Hfull, by simpa [VLCtx.toCtx] using HfullType⟩
end Lean4Lean.VerifyInductive
