import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors
import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructorTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement

/-! The header stage of the restoration substitution of a nested run.

`NestedRun.headerInterpretationSound`: the restoration interpretation
(`Restoration.interpretation`) is a sound interpretation of the lowered header environment (the
source headers followed by the auxiliary headers) into any ordered environment containing the
source header environment, for every context (the invariant `fun _ _ => True`): base constants
and source headers are kept, and each auxiliary header is interpreted by its restoration lambda
`λ params, target levels args`, which is typed at the auxiliary header type in the source header
environment (`NestedRun.headerSetup`). It transports every derivation of the lowered header
environment, in particular the checks the ordinary pipeline performs on the lowered block before
its recursors exist, to the source header environment. The later stages of the substitution are
in `Nested/Restoration/Equations/WF.lean`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace InductiveSignature

/-- The registered ι rules of a well-formed environment are fixed by the restoration
interpretation (projection owners renamed) when the restorable names are fresh there
(`VEnv.WF.pats_fixed_of_avoid`). -/
theorem _root_.Lean4Lean.VEnv.WF.pats_interpretation_fixed_of_restorableFresh {env : VEnv}
    (henv : env.WF) {r : Restoration} {P : List VExpr}
    (hfresh : ∀ name ∈ r.restorableNames, env.constants name = none) :
    ∀ p rr, env.pats p rr → p.ConstsFixed (r.interpretation P) ∧
      rr.1.FixedTermsFixed (r.interpretation P) ∧
      rr.2.FixedTermsFixed (r.interpretation P) := by
  exact henv.pats_fixed_of_avoid hfresh
    (fun _ hc => Restoration.lambdaReplacement_eq_none_of_not_restorable hc)
    (fun _ hc => Restoration.renaming_eq_self hc) (fun _ hc => Restoration.renaming_eq_self hc)

end InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Two expressions with the same retained forall prefix translate, in
contexts with the same translated variables, to terms with the same
translated prefix domains. Translation is syntactic, so the environments may
differ. -/
theorem Expr.SameForallPrefix.takeForalls_of_trExprS
    {env₁ env₂ : VEnv} {Us : List Name} {n : Nat} {left right : Expr}
    (Hsame : Expr.SameForallPrefix n left right) :
    ∀ {Δ₁ Δ₂ : VLCtx} {L R : VExpr} {domains : List VExpr} {tail : VExpr},
      TrExprS.IsUniqueCtx Δ₁ Δ₂ →
      TrExprS env₁ Us Δ₁ left L → TrExprS env₂ Us Δ₂ right R →
      R.takeForalls n = some (domains, tail) →
      ∃ tail', L.takeForalls n = some (domains, tail') := by
  induction Hsame with
  | nil =>
    intro Δ₁ Δ₂ L R domains tail _ _ _ h
    simp only [VExpr.takeForalls, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨L, by simp [VExpr.takeForalls, ← h.1]⟩
  | cons _ ih =>
    intro Δ₁ Δ₂ L R domains tail hΔ HL HR h
    cases HL with
    | forallE _ _ hdL hbL =>
    cases HR with
    | forallE _ _ hdR hbR =>
    have hdom := TrExprS.uniqueCtxEnv hΔ hdL hdR
    subst hdom
    simp only [VExpr.takeForalls, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ds, r⟩, hr, hds⟩ := h
    obtain ⟨tail', htail'⟩ := ih (hΔ.cons .vlam) hbL hbR hr
    refine ⟨tail', ?_⟩
    have hds' : (_ :: ds, r) = (domains, tail) := Option.some.inj hds
    simp only [Prod.mk.injEq] at hds'
    simp [VExpr.takeForalls, htail', ← hds'.1]

/-! ### The restoration is determined by the restoration table data -/

section TableUniqueness

variable {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
  {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}

private theorem heads_nodup {aux : List ContainerSpecialization}
    (D : RestorationTablesAgree decl aux result env auxRec Us₀) :
    ((compilationRestoration decl aux).heads.map (·.auxiliary)).Nodup := by
  rw [compilationRestoration_heads_auxiliary]
  exact D.headNodup

/-- The family data of a specialization is fixed by the tables. -/
theorem RestorationTablesAgree.family_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTablesAgree decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTablesAgree decl aux₁ result env auxRec Us₀)
    {a : ContainerSpecialization} (ha : a ∈ aux₁) :
    ∃ b ∈ aux₀, b.auxiliary = a.auxiliary ∧ b.source.name = a.source.name ∧
      b.levels = a.levels ∧ b.arguments = a.arguments := by
  obtain ⟨nested, hn⟩ := D₁.familyLookup a ha
  obtain ⟨b, hb, hbaux, hbspec⟩ := D₀.familyKey _ nested hn
  obtain ⟨a', ha', ha'aux, ha'spec⟩ := D₁.familyKey _ nested hn
  -- `a` and `a'` have the same family head
  let hA : HeadSpecialization :=
    ⟨a.auxiliary, decl.uvars, decl.nparams, a.source.name, a.levels, a.arguments⟩
  let hA' : HeadSpecialization :=
    ⟨a'.auxiliary, decl.uvars, decl.nparams, a'.source.name, a'.levels, a'.arguments⟩
  have hmemA : hA ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have hmemA' : hA' ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a', ha', List.mem_cons_self⟩
  have h1 := Restoration.find?_of_nodup (heads_nodup D₁) hmemA
  have h2 := Restoration.find?_of_nodup (heads_nodup D₁) hmemA'
  have hauxEq : hA'.auxiliary = hA.auxiliary := ha'aux
  rw [hauxEq, h1] at h2
  have hAA : hA = hA' := Option.some.inj h2
  simp only [hA, hA', HeadSpecialization.mk.injEq] at hAA
  obtain ⟨-, -, -, hsrc, hlev, hargs⟩ := hAA
  obtain ⟨hs, hl, hr⟩ := AuxiliaryContainerApp.unique hbspec ha'spec
  exact ⟨b, hb, hbaux, hs.trans hsrc.symm, hl.trans hlev.symm,
    hr.trans hargs.symm⟩

/-- Every head of one table is a head of any other table of the same run. -/
theorem RestorationTablesAgree.find_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTablesAgree decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTablesAgree decl aux₁ result env auxRec Us₀)
    {n : Name} {h : HeadSpecialization}
    (hfind : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) =
      some h) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) = some h := by
  have hmem := List.mem_of_find?_eq_some hfind
  have hn : h.auxiliary = n := by simpa using List.find?_some hfind
  subst hn
  obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hmem
  obtain ⟨b, hb, hbaux, hbsrc, hblev, hbargs⟩ := D₀.family_transfer D₁ ha
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
  rcases hh with rfl | ⟨ctor, hctor, rfl⟩
  · let hB : HeadSpecialization :=
      ⟨b.auxiliary, decl.uvars, decl.nparams, b.source.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have := Restoration.find?_of_nodup (heads_nodup D₀) hmemB
    simp only [hB, hbaux, hbsrc, hblev, hbargs] at this
    exact this
  · obtain ⟨info, hc, hind⟩ := D₁.ctorInstalled a ha ctor hctor
    obtain ⟨ctor', hctor', hcname⟩ :=
      D₀.ctorLookup _ info hc b hb (hind.trans hbaux.symm)
    have hrenA : (a.constructorName ctor).replacePrefix a.auxiliary a.source.name =
        ctor.name :=
      (namePrefix_of_replacePrefix_ne (D₁.ctorRenamed a ha ctor hctor)).replacePrefix_replacePrefix _
    have hrenB : (b.constructorName ctor').replacePrefix b.auxiliary b.source.name =
        ctor'.name :=
      (namePrefix_of_replacePrefix_ne (D₀.ctorRenamed b hb ctor' hctor')).replacePrefix_replacePrefix _
    have hname : ctor'.name = ctor.name := by
      rw [← hrenA, ← hrenB, ← hcname, hbaux, hbsrc]
    let hB : HeadSpecialization :=
      ⟨b.constructorName ctor', decl.uvars, decl.nparams, ctor'.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨ctor', hctor', rfl⟩)⟩
    have := Restoration.find?_of_nodup (heads_nodup D₀) hmemB
    simp only [hB, ← hcname, hname, hblev, hbargs] at this
    exact this

theorem RestorationTablesAgree.find_eq {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTablesAgree decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTablesAgree decl aux₁ result env auxRec Us₀) (n : Name) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) =
      (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) := by
  cases h1 : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) with
  | some h => exact D₀.find_transfer D₁ h1
  | none =>
    cases h0 : (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) with
    | none => rfl
    | some h =>
      have := D₁.find_transfer D₀ h0
      rw [h1] at this
      cases this

theorem Restoration.go_congr {r r' : Restoration}
    (hfind : ∀ n, r.heads.find? (fun h => h.auxiliary == n) =
      r'.heads.find? (fun h => h.auxiliary == n))
    (hrec : ∀ n, r.recursorName n = r'.recursorName n) :
    ∀ (e : VExpr) (args : List VExpr),
      Restoration.expr.go r e args = Restoration.expr.go r' e args := by
  intro e
  induction e with
  | bvar | sort => intro args; rfl
  | const name levels =>
    intro args
    simp only [Restoration.expr.go, hfind name, hrec name]
  | app fn arg ihf iha =>
    intro args
    simp only [Restoration.expr.go, iha, ihf]
  | lam d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | forallE d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | proj n i m ih =>
    intro args
    simp only [Restoration.expr.go, ih]

/-- **The restoration is determined by the restoration table data.** -/
theorem RestorationTablesAgree.expr_eq {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTablesAgree decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTablesAgree decl aux₁ result env auxRec Us₀) (e : VExpr) :
    (compilationRestoration decl aux₀).expr e = (compilationRestoration decl aux₁).expr e :=
  Restoration.go_congr (D₀.find_eq D₁)
    (fun n => (D₀.recursorName n).trans (D₁.recursorName n).symm) e []

theorem RestorationTablesAgree.restorable_transfer {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTablesAgree decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTablesAgree decl aux₁ result env auxRec Us₀) {n : Name}
    (hn : n ∈ (compilationRestoration decl aux₁).restorableNames) :
    n ∈ (compilationRestoration decl aux₀).restorableNames := by
  simp only [Restoration.restorableNames, List.mem_append] at hn ⊢
  rcases hn with hn | hn
  · left
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hn
    have h1 := Restoration.find?_of_nodup (heads_nodup D₁) hh
    have h0 := D₀.find_transfer D₁ h1
    exact List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some h0, rfl⟩
  · right
    rw [compilationRestoration_recursors_fst] at hn ⊢
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    obtain ⟨b, hb, hbaux, -⟩ := D₀.family_transfer D₁ ha
    exact List.mem_map.mpr ⟨b, hb, by rw [hbaux]⟩

end TableUniqueness

/-- The setup shared by the stages: the lowered header environment splits as
the source headers followed by the auxiliary headers, and the auxiliary
headers are typed by their restoration lambdas in the source header
environment. -/
theorem NestedRun.headerSetup
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
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
    (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        (sourceDecl.typeConstants ++
          (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map
            VInductiveType.toVConstVal) =
        some E.lowered.constructors.headerVEnv ∧
      (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
        familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.nparams = E.lowered.signature.params.length) ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ arg ∈ h.arguments,
        arg.ClosedN h.nparams) ∧
      (∀ i (hi : i < E.lowered.signature.params.length),
        E.lowered.signature.params[i].ClosedN i) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ ci,
        E.lowered.constructors.headerVEnv.constants h.auxiliary = some ci →
        ci.type.containsAnyConst
            (compilationRestoration sourceDecl auxiliaries).restorableNames = false ∧
        envTypes.HasType ci.uvars []
          (VExpr.wrapLams E.lowered.signature.params
            (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type) := by
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hsuffixNodup :
      (familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ++
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map
          (fun t => t.name.str "rec")).Nodup := by
    refine hnodup.sublist (List.Sublist.append ?_ ((List.drop_sublist _ _).map _))
    conv => rhs; rw [← List.take_append_drop sourceDecl.types.length
      E.lowered.loweredDecl.types]
    simp only [familyNames, List.flatMap_append]
    exact List.sublist_append_right _ _
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.lowered.constructors.parameterScope.toCtx.reverse).reverse
      E.lowered.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorCheck.parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hscoped := auxiliarySpecializations_scoped Haux Hexpansion hsuffixNodup
  have hinit : E.lowered.Hc'.venv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.lowered_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.lowered.loweredDecl.typeConstants =
        some E.lowered.constructors.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.lowered.loweredDecl.typeConstants =
          some E.lowered.constructors.headerVEnv) hinit)
      E.lowered.constructors.core.typesAdded
  have Hsource := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hprefix : sourceDecl.typeConstants =
      E.lowered.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.sourceCore.sourceTypeValues
    rw [E.sourceCoreDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hloweredSplit : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      (sourceDecl.typeConstants ++
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map
          VInductiveType.toVConstVal) =
        some E.lowered.constructors.headerVEnv := by
    rw [hprefix, VInductDecl.typeConstants, List.map_drop, List.take_append_drop]
    exact hloweredTypes
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hparams : E.lowered.signature.params =
      E.lowered.constructors.parameterScope.toCtx.reverse :=
    E.lowered.recursorConstruction.generator.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.lowered.signature.params.reverse
      E.lowered.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  have hPclosed : ∀ i (hi : i < E.lowered.signature.params.length),
      E.lowered.signature.params[i].ClosedN i := by
    intro i hi
    simpa using OnCtx.reverse_getElem_closedN henvTypes (Γ := [])
      (by simpa using hP.isType) i hi
  have hordered := henvTypes.ordered
  have hscopedNodup := hscoped.1
  have hfamilyHead : ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∃ a ∈ auxiliaries, ∃ g,
        SpecializationGenerates (ves.venv (if isUnsafe then .unsafe else .safe))
          envTypes E.lowered.headers.commonParameterContext sourceDecl a g ∧
        VInductDecl.NestedTypeExpansion (ves.venv (if isUnsafe then .unsafe else .safe))
          sourceDecl (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated) g t := by
    intro t ht
    obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexpansion t ht
    obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
    exact ⟨a, ha, g, hev, hexp⟩
  have hheadsParams : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.lowered.signature.params.length := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    have hn : h.nparams = sourceDecl.nparams := by
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨_, _, rfl⟩ <;> rfl
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    obtain ⟨sourceParams, hlen, hctx, -⟩ := hev.application
    rw [hn, ← hlen]
    have h1 := hctx.length_eq
    have h2 := hP.length_eq
    simp only [List.length_reverse] at h1 h2
    omega
  refine ⟨hloweredSplit, hheadNames, hheadsParams,
    fun h hh arg harg => (hscoped.2.2.1 h hh).2 arg harg, hPclosed, hscoped, ?_⟩
  intro h hh ci hci
  rcases lookup_of_addConstVals_append hadded hloweredSplit hci with
    henvT | ⟨entry, hentry, hn, hval⟩
  · rw [hfreshAll _ (List.mem_append_left _ (List.mem_map_of_mem hh))] at henvT; cases henvT
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
  obtain ⟨a, ha, g, hev, hexp⟩ := hfamilyHead t ht
  have hfh : InductiveSignature.HeadSpecialization.mk a.auxiliary sourceDecl.uvars
      sourceDecl.nparams a.source.name a.levels a.arguments ∈
      (compilationRestoration sourceDecl auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have heqh := List.nodup_map_inj hscopedNodup hh hfh
    (hn.symm.trans (hexp.name.trans hev.auxiliary.symm))
  subst heqh
  subst hval
  obtain ⟨sourceParams, hlen, hctx, honctx, htyping, hgtype, -⟩ := hev.application
  have htype : envTypes.IsDefEqU sourceDecl.uvars [] g.type t.type :=
    hexp.type.mono (VEnv.addConstVals_le hadded)
  obtain ⟨_, htypeD⟩ := htype
  have huvars : t.uvars = sourceDecl.uvars := hexp.uvars.trans hev.generatedUvars
  change t.type.containsAnyConst _ = false ∧
    envTypes.HasType t.uvars [] _ t.type
  rw [huvars]
  refine ⟨(htypeD.noFreshConsts henvTypes hfreshAll (by intro _ h; simp at h)).2.1, ?_⟩
  have hPS : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.lowered.signature.params.reverse sourceParams.reverse :=
    VEnv.IsDefEqCtx.trans_empty henvTypes hP (hctx.symm hordered)
  have htypingP := htyping.defeqDFC hordered (hPS.symm hordered)
  have hlam : envTypes.HasType sourceDecl.uvars []
      (VExpr.wrapLams E.lowered.signature.params
        (VExpr.mkApps (.const a.source.name a.levels) a.arguments))
      (VExpr.wrapForalls E.lowered.signature.params
        (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments)) :=
    VEnv.HasType.wrapLams (ctx := []) (by simpa using hP.isType) (by simpa using htypingP)
  obtain ⟨u, hu⟩ := htyping.isType hordered honctx
  have hforalls := VExpr.wrapForalls_defeqCtx henvTypes hPS ⟨u, hu⟩ ⟨_, hu⟩
  have hchain : envTypes.IsDefEqU sourceDecl.uvars []
      (VExpr.wrapForalls E.lowered.signature.params
        (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments))
      t.type :=
    VEnv.IsDefEqU.trans henvTypes trivial hforalls
      (VEnv.IsDefEqU.trans henvTypes trivial hgtype.symm ⟨_, htypeD⟩)
  exact hlam.defeqU_r henvTypes trivial hchain

/-- The head found for a name occurring among the head names. -/
theorem Restoration.find?_of_mem_heads {r : Restoration} {n : Name}
    (h : n ∈ r.heads.map (·.auxiliary)) :
    ∃ hd, r.heads.find? (fun h => h.auxiliary == n) = some hd ∧ hd ∈ r.heads ∧
      hd.auxiliary = n := by
  cases hf : r.heads.find? (fun h => h.auxiliary == n) with
  | none =>
    obtain ⟨hd, hmem, rfl⟩ := List.mem_map.mp h
    exact absurd (List.find?_eq_none.mp hf hd hmem) (by simp)
  | some hd =>
    exact ⟨hd, rfl, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- **The header stage**: the restoration interpretation is sound from the lowered header
environment into any ordered environment containing the source header environment, in every
context. -/
theorem NestedRun.headerInterpretationSound
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
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
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    {envT : VEnv} (hT : envT.OrderedStrong) (hle : envTypes ≤ envT) :
    ((compilationRestoration sourceDecl auxiliaries).interpretation
      E.lowered.signature.params).Sound envT
      E.lowered.constructors.headerVEnv fun _ _ => True := by
  obtain ⟨hsplit, hheadNames, hnp, hargs, hPclosed, -, hrepl⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hbase : (ves.venv (if isUnsafe then .unsafe else .safe)).WF := TrEnv'.wf wf.tr
  have hbaseLe := VEnv.addConstVals_le hadded
  have hbaseFresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants n = none :=
    fun n hn => hbaseLe.constants_eq_none_left (hfreshAll n hn)
  have hon := hbase.onTypes_noFreshConsts hbaseFresh
  have hnotR : ∀ {env : VEnv} {c ci},
      (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
        env.constants n = none) →
      env.constants c = some ci →
      c ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
    intro env c ci hf hc hmem
    rw [hf c hmem] at hc
    cases hc
  have hclosed := Restoration.interpretation_closed hnp hargs hPclosed
  have S₀ : ((compilationRestoration sourceDecl auxiliaries).interpretation
      E.lowered.signature.params).Sound envT (ves.venv (if isUnsafe then .unsafe else .safe))
      fun _ _ => True := by
    refine VEnv.Interpretation.Sound.of_le hclosed
      (Restoration.interpretation_preservesTelescopes _ _) hT hbase.ordered
      (hbaseLe.trans hle) ?_ ?_ ?_
    · intro c ci hc
      have hn := hnotR hbaseFresh hc
      obtain ⟨_, hty, -⟩ := hon.1 hc
      exact ⟨Restoration.lambdaReplacement_eq_none_of_not_restorable hn,
        Restoration.renaming_eq_self hn, Restoration.renaming_eq_self hn,
        Restoration.interpretation_expr_eq_self hty⟩
    · intro df hdf
      obtain ⟨⟨hl, ht⟩, hr, -⟩ := hon.2 hdf
      exact ⟨Restoration.interpretation_expr_eq_self hl,
        Restoration.interpretation_expr_eq_self hr, Restoration.interpretation_expr_eq_self ht⟩
    · intro p rr hp
      exact hbase.pats_interpretation_fixed_of_restorableFresh hbaseFresh p rr hp
  refine S₀.addConstVals hsplit ?_
  intro c hc
  rcases List.mem_append.mp hc with hsrc | haux
  · have hget := VEnv.addConstVals_get hadded hsrc
    have hn := hnotR hfreshAll hget
    have hρ := Restoration.lambdaReplacement_eq_none_of_not_restorable
      (domains := fun _ => E.lowered.signature.params) hn
    obtain ⟨_, hty, -⟩ := (henvTypes.onTypes_noFreshConsts hfreshAll).1 hget
    obtain ⟨u, hu⟩ := henvTypes.ordered.constWF hget
    refine ⟨fun t ht => (by rw [Restoration.interpretation_consts, hρ] at ht; cases ht), fun _ => ?_⟩
    refine ⟨c.toVConstant, by
      rw [Restoration.interpretation_rename, Restoration.renaming_eq_self hn]
      exact hle.constants hget, rfl, u, ?_⟩
    rw [Restoration.interpretation_expr_eq_self hty]
    exact hu.mono hle
  · have hget := VEnv.addConstVals_get hsplit (List.mem_append_right _ haux)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp haux
    have hmem : t.name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
        (·.auxiliary) := by
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, ht, .inl rfl⟩
    obtain ⟨hd, hf, hdmem, hdaux⟩ := Restoration.find?_of_mem_heads hmem
    have hget' : E.lowered.constructors.headerVEnv.constants hd.auxiliary =
        some t.toVConstVal.toVConstant := by rw [hdaux]; exact hget
    obtain ⟨hfree, htyped⟩ := hrepl hd hdmem _ hget'
    refine ⟨fun t' ht' => ?_, fun hnone => ?_⟩
    · simp only [Restoration.interpretation_consts, Restoration.lambdaReplacement, hf,
        Option.map_some, Option.some.injEq] at ht'
      subst ht'
      rw [Restoration.interpretation_expr_eq_self hfree]
      exact htyped.mono hle
    · simp [Restoration.lambdaReplacement, hf] at hnone

/-- Names of the source prefix of the lowered declaration are not
restorable. -/
theorem not_restorable_of_take {types : List VInductiveType} {k : Nat}
    {sourceDecl : VInductDecl} {auxiliaries : List ContainerSpecialization}
    (hnodup : (familyNames types ++ types.map (fun t => t.name.str "rec")).Nodup)
    (hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (types.drop k))
    (hauxNames : auxiliaries.map (·.auxiliary) = (types.drop k).map (·.name))
    {n : Name} (hn : n ∈ familyNames (types.take k)) :
    n ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro hmem
  have hsplit : familyNames types = familyNames (types.take k) ++ familyNames (types.drop k) := by
    conv => lhs; rw [← List.take_append_drop k types]
    simp only [familyNames, List.flatMap_append]
  obtain ⟨hfam, -, hdisj⟩ := List.nodup_append.mp hnodup
  rcases List.mem_append.mp hmem with hh | hr
  · rw [hheadNames] at hh
    rw [hsplit] at hfam
    exact (List.nodup_append.mp hfam).2.2 n hn n hh rfl
  · rw [compilationRestoration_recursors_fst] at hr
    have hr' : n ∈ types.map (fun t => t.name.str "rec") := by
      have : auxiliaries.map (fun a => a.auxiliary.str "rec") =
          (types.drop k).map (fun t => t.name.str "rec") := by
        have := congrArg (List.map (fun n : Name => n.str "rec")) hauxNames
        simpa [List.map_map, Function.comp_def] using this
      rw [this] at hr
      exact List.map_subset _ (List.drop_subset _ _) hr
    have hn' : n ∈ familyNames types := by
      rw [hsplit]; exact List.mem_append_left _ hn
    exact hdisj n hn' n hr' rfl

/-- A structure registered in the base environment is a base constant, so its
name is not restorable. -/
theorem NestedRun.baseProjection_not_restorable
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
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
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    {S : Name} {info : VProjectionInfo}
    (hS : (ves.venv (if isUnsafe then .unsafe else .safe)).projections S info) :
    S ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro hmem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    (wf.tr (safety := if isUnsafe then .unsafe else .safe)).wf.ordered.projectionShape hS
  have h := (VEnv.addConstVals_le hadded).constants hlookup
  rw [E.restorableNames_fresh hadded Haux Hexpansion hnodup S hmem] at h
  cases h

section Run

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

end Run

end VerifyInductive
end Lean4Lean
