import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.WF
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryProjections

/-! The container fields of `RestorationSubstitutionPremises`
(`Nested/Restoration/Equations/WF.lean`): the typing of the restoration lambdas of
the auxiliary constructors (`auxiliaryConstructors`) and the transport of the
projection rules of the lowered declaration (`projections`).

**Auxiliary constructors.** The restoration lambda of an auxiliary
constructor head is `λ params, J.c levels args`, where `J.c` is a constructor
of the certified container `J` of the specialization. The container's
installation certificate records its source parameter formation: the
parameter prefix of the constructor type of `J.c` is definitionally the
parameter prefix of the family type of `J`
(`InstalledBelow.ctorParameterContext`). The specialization
types the family application `J levels args` in the source parameter
context, so the constructor application `J.c levels args` has the
instantiated constructor type (`HasType.const_mkApps_of_family`). Closing over
the signature parameters gives the type of the direct constructor, which is
definitionally the generated constructor type, the syntactic restoration of
the lowered constructor type.

**Projections.** The projection rules of the lowered declaration are transported in
well-formed image contexts (`ProjectionClause` for `VEnv.TypedCtx`,
`Nested/Restoration/Equations/ProjectionRenaming.lean` and `Nested/Restoration/AuxiliaryProjections.lean`), where beta
subject reduction applies.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Generic telescope lemmas -/

/-- Definitionally equal forall telescopes of the same length have
definitionally equal domain contexts. -/
theorem VEnv.IsDefEqU.wrapForalls_defeqCtx_inv {env : VEnv} {U : Nat} (henv : env.WF)
    {Γ₀ : List VExpr} :
    ∀ {A A' : List VExpr} {X X' : VExpr} {Γ₁ Γ₂ : List VExpr},
      A.length = A'.length →
      VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → OnCtx Γ₁ (env.IsType U) →
      env.IsDefEqU U Γ₁ (VExpr.wrapForalls A X) (VExpr.wrapForalls A' X') →
      VEnv.IsDefEqCtx env U Γ₀ (A.reverse ++ Γ₁) (A'.reverse ++ Γ₂)
  | [], [], _, _, _, _, _, hctx, _, _ => by simpa using hctx
  | [], _ :: _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp at h
  | d :: A, d' :: A', X, X', Γ₁, Γ₂, hlen, hctx, hΓ, H => by
    obtain ⟨⟨u, hd⟩, _, hb⟩ := Lean4Lean.VEnv.IsDefEqU.forallE_inv henv hΓ H
    have hctx' : VEnv.IsDefEqCtx env U Γ₀ (d :: Γ₁) (d' :: Γ₂) := .succ hctx hd
    have hΓ' : OnCtx (d :: Γ₁) (env.IsType U) := ⟨hΓ, u, hd.hasType.1⟩
    have := VEnv.IsDefEqU.wrapForalls_defeqCtx_inv henv (A := A) (A' := A')
      (X := X) (X' := X') (by simpa using hlen) hctx' hΓ' ⟨_, hb⟩
    simpa [List.reverse_cons, List.append_assoc] using this

/-- A constant whose type is a forall telescope whose parameter prefix is
definitionally that of another constant can be applied to every argument
spine typed by that other constant's prefix. -/
theorem VEnv.HasType.const_mkApps_of_family {env : VEnv} {U N : Nat} (henv : env.WF)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {fam ctor : Name} {cf cc : VConstant}
    (hf : env.constants fam = some cf) (hc : env.constants ctor = some cc)
    {famDoms ctorDoms : List VExpr} {famRest ctorRest : VExpr}
    (hfty : cf.type = VExpr.wrapForalls famDoms famRest)
    (hcty : cc.type = VExpr.wrapForalls ctorDoms ctorRest)
    (hfu : cf.uvars = N) (hcu : cc.uvars = N)
    (hctx : VEnv.IsDefEqCtx env N [] famDoms.reverse ctorDoms.reverse)
    {levels : List VLevel} (hlev : ∀ l ∈ levels, l.WF U) (hlen : levels.length = N)
    {args : List VExpr} (hargs : args.length = famDoms.length) {T : VExpr}
    (happ : env.HasType U Γ (VExpr.mkApps (.const fam levels) args) T) :
    env.HasType U Γ (VExpr.mkApps (.const ctor levels) args)
      (VExpr.instantiateForallPrefix (cc.type.instL levels) args) := by
  have hordered := henv.ordered
  have hctxL := VEnv.IsDefEqCtx.instL hlev hctx
  simp only [List.map_nil, List.map_reverse] at hctxL
  have hf0 : env.HasType U [] (.const fam levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) := by
    have := VEnv.HasType.const (Γ := []) hf hlev (by rw [hfu]; exact hlen)
    rwa [hfty, VExpr.instL_wrapForalls] at this
  have hc0 : env.HasType U [] (.const ctor levels)
      (VExpr.wrapForalls (ctorDoms.map (VExpr.instL levels)) (ctorRest.instL levels)) := by
    have := VEnv.HasType.const (Γ := []) hc hlev (by rw [hcu]; exact hlen)
    rwa [hcty, VExpr.instL_wrapForalls] at this
  have hcT := VEnv.IsType.wrapForalls_inv hordered (ctx := []) trivial
    (VEnv.IsDefEq.isType hordered trivial hc0)
  have hY : env.IsType U (famDoms.map (VExpr.instL levels)).reverse (ctorRest.instL levels) := by
    have h2 : env.IsType U (ctorDoms.map (VExpr.instL levels)).reverse
        (ctorRest.instL levels) := by simpa using hcT.2
    exact h2.defeqDFC hordered (hctxL.symm hordered)
  obtain ⟨u, hu⟩ := hY
  have hW := VExpr.wrapForalls_defeqCtx henv (P := ctorDoms.map (VExpr.instL levels))
    (Q := famDoms.map (VExpr.instL levels)) (hctxL.symm hordered) ⟨u, hu⟩ ⟨_, hu⟩
  have hc1 := hc0.defeqU_r henv trivial hW
  have hcΓ : env.HasType U Γ (.const ctor levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (ctorRest.instL levels)) :=
    hc1.weak0 hordered
  have hfΓ : env.HasType U Γ (.const fam levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) :=
    hf0.weak0 hordered
  have Hdom : SameTelescopeDomains args.length
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (ctorRest.instL levels))
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) := by
    have := SameTelescopeDomains.wrapForalls (famDoms.map (VExpr.instL levels))
      (ctorRest.instL levels) (famRest.instL levels)
    rwa [List.length_map, ← hargs] at this
  have H := VEnv.HasType.mkApps_sameTelescopeDomains_exact henv hΓ Hdom hcΓ hfΓ ⟨_, happ⟩
  have hlenC : ctorDoms.length = famDoms.length := by
    have := hctx.length_eq
    simp only [List.length_reverse] at this
    omega
  rw [VExpr.applyForallType_eq_instantiateForallPrefix,
    VExpr.instantiateForallPrefix_wrapForalls _ _ _ (by simpa using hargs.symm)] at H
  rw [hcty, VExpr.instL_wrapForalls,
    VExpr.instantiateForallPrefix_wrapForalls _ _ _ (by simp [hlenC, hargs])]
  exact H

/-! ### Installed containers -/

private theorem addConst_le_target' {base added current : VEnv} {name : Name} {ci : VConstant}
    (hle : base ≤ current) (hadd : base.addConst name ci = some added)
    (hvalue : current.constants name = some ci) : added ≤ current := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    refine ⟨?_, hle.defeqs, hle.pats, hle.projections⟩
    intro n value hv
    change (if name = n then some ci else base.constants n) = some value at hv
    split at hv
    · rename_i hn
      cases hn
      cases Option.some.inj hv
      exact hvalue
    · exact hle.constants hv

private theorem addConstVals_le_target' {base added current : VEnv} {values : List VConstVal}
    (hle : base ≤ current) (hadd : base.addConstVals values = some added)
    (hvalues : ∀ value ∈ values, current.constants value.name = some value.toVConstant) :
    added ≤ current := by
  induction values generalizing base with
  | nil =>
    have he : base = added := Option.some.inj hadd
    cases he
    exact hle
  | cons value values ih =>
    cases hv : base.addConst value.name value.toVConstant with
    | none => simp [VEnv.addConstVals, hv] at hadd
    | some next =>
      have ht : next.addConstVals values = some added := by
        simpa only [VEnv.addConstVals, hv, bind, Option.bind_some] using hadd
      exact ih (addConst_le_target' hle hv (hvalues value (.head _))) ht
        fun value hmem => hvalues value (.tail _ hmem)


/-- The parameter prefix of every constructor type of an installed container
is definitionally the parameter prefix of its family type, given that the
family type has a syntactic parameter prefix. -/
theorem _root_.Lean4Lean.VEnv.InstalledBelow.ctorParameterContext {env : VEnv}
    {decl : VInductDecl} (henv : env.WF) (H : VEnv.InstalledBelow env decl)
    {type : VInductiveType} (htype : type ∈ decl.types)
    {ctor : VConstVal} (hctor : ctor ∈ type.ctors)
    (hpre : HasForallPrefix type.type decl.nparams) :
    ∃ famDoms famRest ctorDoms ctorRest,
      type.type = VExpr.wrapForalls famDoms famRest ∧
      ctor.type = VExpr.wrapForalls ctorDoms ctorRest ∧
      famDoms.length = decl.nparams ∧
      VEnv.IsDefEqCtx env decl.uvars [] famDoms.reverse ctorDoms.reverse := by
  obtain ⟨_, hfacts⟩ := H.familyFacts
  have hparams : ∃ base', base' ≤ env ∧ VInductDecl.SourceParameterWF base' decl := by
    cases H with
    | @intro _ _ base block installed hsource hformation hcompile _ _ hinstall hle =>
      have hbase : base ≤ env := (VEnv.addInduct_le hinstall).trans hle
      cases hformation with
      | ordinary hwf => exact ⟨base, hbase, hwf.sourceParameterWF⟩
      | nested hnested hle' =>
        cases hnested with
        | intro _ _ hparams _ _ _ _ => exact ⟨_, hle'.trans hbase, hparams⟩
  obtain ⟨base', hbase', params, envT', htypes', hshapes, hctorShapes, -⟩ := hparams
  have hT'le : envT' ≤ env := addConstVals_le_target' hbase' htypes' (by
    intro value hvalue
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvalue
    exact (hfacts t ht).1)
  obtain ⟨normalized, ownF, afterF, -, -, exprType, hdef, htakeF, -, hPF, -⟩ :=
    hshapes type htype
  obtain ⟨ctorDoms, ctorRest, htakeC, hPC⟩ := hctorShapes type htype ctor hctor
  obtain ⟨hctorEq, hctorLen⟩ := VExpr.takeForalls_rebuild htakeC
  obtain ⟨hnormEq, hnormLen⟩ := VExpr.takeForalls_rebuild htakeF
  obtain ⟨domains, body, htypeEq, hn⟩ := hpre
  have hsplit : type.type = VExpr.wrapForalls (domains.take decl.nparams)
      (VExpr.wrapForalls (domains.drop decl.nparams) body) := by
    rw [htypeEq, ← VExpr.wrapForalls_append, List.take_append_drop]
  have hfamLen : (domains.take decl.nparams).length = decl.nparams := by
    simp [List.length_take, Nat.min_eq_left hn]
  have hdefE : env.IsDefEqU decl.uvars [] (VExpr.wrapForalls (domains.take decl.nparams)
      (VExpr.wrapForalls (domains.drop decl.nparams) body))
      (VExpr.wrapForalls ownF afterF) := by
    rw [← hsplit, ← hnormEq]
    exact ⟨_, hdef.mono hbase'⟩
  have h1 := VEnv.IsDefEqU.wrapForalls_defeqCtx_inv henv (Γ₀ := []) (Γ₁ := []) (Γ₂ := [])
    (by rw [hfamLen, hnormLen]) .zero trivial hdefE
  simp only [List.append_nil] at h1
  have hPF' : VEnv.IsDefEqCtx env decl.uvars [] params.reverse ownF.reverse :=
    VEnv.IsDefEqCtx.mono hbase' hPF
  have hPC' : VEnv.IsDefEqCtx env decl.uvars [] params.reverse ctorDoms.reverse :=
    VEnv.IsDefEqCtx.mono hT'le hPC
  exact ⟨_, _, ctorDoms, ctorRest, hsplit, hctorEq, hfamLen,
    VEnv.IsDefEqCtx.trans_empty henv h1
      (VEnv.IsDefEqCtx.trans_empty henv (hPF'.symm henv.ordered) hPC')⟩

/-- **Typing of the restoration lambdas of the auxiliary constructors**, for
a specialization list with its typing and a restoring expansion of the
lowered auxiliary families: the restoration lambda `λ params, J.c levels args`
of the head of a lowered auxiliary constructor has, in the source header
environment, the restoration of the lowered constructor type (which is the
generated constructor type). -/
theorem auxiliaryConstructorLambdas_hasType
    {base envTypes : VEnv} {paramCtx params : List VExpr} {decl : VInductDecl}
    {auxiliaries : List ContainerSpecialization}
    {generated targets : List VInductiveType}
    (henv : envTypes.WF) (hle : base ≤ envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl
        ((compilationRestoration decl auxiliaries).RestoringLeaf (VLevel.params decl.uvars)))
      generated targets)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hnodup : ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary)).Nodup)
    (hfresh : ∀ name ∈ (compilationRestoration decl auxiliaries).restorableNames,
      envTypes.constants name = none)
    (hlevels : ∀ t ∈ targets, ∀ lc ∈ t.ctors,
      lc.type.ConstLevelsAt ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary))
        (VLevel.params decl.uvars)) :
    ∀ t ∈ targets, ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration decl auxiliaries).heads,
      h.auxiliary = lc.name →
      ∃ restored, (compilationRestoration decl auxiliaries).expr lc.type = some restored ∧
        envTypes.HasType decl.uvars []
          (VExpr.wrapLams params (VExpr.mkApps (.const h.target h.levels) h.arguments))
          restored := by
  intro t ht lc hlc h hh hname
  have hordered := henv.ordered
  obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexp t ht
  obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
  obtain ⟨gc, hgc, hc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hexp.constructors lc hlc
  obtain ⟨sp, -, hspCtx, hspOn, htyping, -, hctors⟩ := hev.application
  obtain ⟨ctor, hctor, hdc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors gc hgc
  -- the head of `lc` is the constructor head of `a` at `ctor`
  let hA : HeadSpecialization :=
    { auxiliary := a.constructorName ctor, uvars := decl.uvars, nparams := decl.nparams,
      target := ctor.name, levels := a.levels, arguments := a.arguments }
  have hAmem : hA ∈ (compilationRestoration decl auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
  have hAname : hA.auxiliary = lc.name := by
    change a.constructorName ctor = lc.name
    rw [hc.name, hdc.name, ← hev.auxiliary]
    rfl
  have heq := List.nodup_map_inj hnodup hh hAmem (hname.trans hAname.symm)
  subst heq
  -- restoration of the lowered constructor type
  obtain ⟨_, hgd⟩ := hdc.type
  have hfree : gc.type.containsAnyConst
      (compilationRestoration decl auxiliaries).restorableNames = false :=
    (hgd.hasType.1.noFreshConsts henv hfresh (by intro _ h; simp at h)).1
  refine ⟨gc.type, hc.type.restore hfree (hlevels t ht lc hlc), ?_⟩
  -- typing of the container constructor application
  have hinst := hev.installed.mono hle
  have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  obtain ⟨famDoms, famRest, ctorDoms, ctorRest, hfty, hcty, hfamLen, hctx⟩ :=
    hinst.ctorParameterContext henv hsrc hctor
      (by rw [← hev.argumentsLength]; exact hev.familyForallPrefix)
  have hfconst : envTypes.constants a.source.name = some a.source.toVConstant := by
    have := hinst.familyConstant a.family.val a.family.isLt
    exact this
  have hcconst := hinst.constructorConstant_mem hsrc hctor
  have hcapp := VEnv.HasType.const_mkApps_of_family henv hspOn hfconst hcconst hfty hcty
    (hinst.typeUvars _ hsrc)
    (hinst.constructorUvars _ (List.mem_flatMap.mpr ⟨_, hsrc, hctor⟩))
    hctx hev.levelsWF hev.levelsLength (by rw [hfamLen, hev.argumentsLength]) htyping
  have hPS : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse sp.reverse :=
    VEnv.IsDefEqCtx.trans_empty henv hparams (hspCtx.symm hordered)
  have hcappP := hcapp.defeqDFC hordered (hPS.symm hordered)
  have hlam : envTypes.HasType decl.uvars []
      (VExpr.wrapLams params (VExpr.mkApps (.const ctor.name a.levels) a.arguments))
      (VExpr.wrapForalls params
        (VExpr.instantiateForallPrefix (ctor.type.instL a.levels) a.arguments)) :=
    VEnv.HasType.wrapLams (ctx := []) (by simpa using hPS.isType) (by simpa using hcappP)
  obtain ⟨u, hu⟩ := VEnv.IsDefEq.isType hordered hspOn hcapp
  have hforalls := VExpr.wrapForalls_defeqCtx henv hPS ⟨u, hu⟩ ⟨_, hu⟩
  exact hlam.defeqU_r henv trivial
    (VEnv.IsDefEqU.trans henv trivial hforalls ⟨_, hgd.symm⟩)

/-- **The `auxiliaryConstructors` field of `RestorationSubstitutionPremises`**,
for every restoration table of the run. The specialization list of
`restorationTablesRestoringAll` carries the hypotheses of
`auxiliaryConstructorLambdas_hasType`; its heads and restoration agree with
those of every other table (`RestorationTablesAgree.find_transfer`,
`RestorationTablesAgree.expr_eq`). -/
theorem NestedRun.restoredEquationAuxiliaryConstructors_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ envTypes : VEnv,
        (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
          sourceDecl.typeConstants = some envTypes →
        ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
          ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
            h.auxiliary = lc.name →
            ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                some restored ∧
              envTypes.HasType sourceDecl.uvars []
                (VExpr.wrapLams E.lowered.signature.params
                  (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored := by
  intro auxiliaries D envTypes' hadded' t ht lc hlc h hh hname
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', -,
      HauxRestoring, -⟩
  have heq : envTypes' = envTypes := Option.some.inj (hadded'.symm.trans hadded)
  rw [heq]
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hlevels : ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt
        ((compilationRestoration sourceDecl aux').heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.lowered.constructors.parameterScope.toCtx.reverse).reverse
      E.lowered.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorCheck.parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hparams : E.lowered.signature.params =
      E.lowered.constructors.parameterScope.toCtx.reverse :=
    E.lowered.recursorConstruction.generator.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.lowered.signature.params.reverse
      E.lowered.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  have hheadsNodup : ∀ {aux : List ContainerSpecialization},
      RestorationTablesAgree sourceDecl aux result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ((compilationRestoration sourceDecl aux).heads.map (·.auxiliary)).Nodup := by
    intro aux Daux
    rw [compilationRestoration_heads_auxiliary]
    exact Daux.headNodup
  -- transfer the head to the table of `restorationTablesRestoringAll`
  have hfind := Restoration.find?_of_nodup (hheadsNodup D) hh
  have hfind' := D'.find_transfer D hfind
  have hmem' := List.mem_of_find?_eq_some hfind'
  obtain ⟨restored, hr, hty⟩ := auxiliaryConstructorLambdas_hasType henvTypes
    (VEnv.addConstVals_le hadded) Haux HauxRestoring hP (hheadsNodup D') hfreshAll hlevels
    t ht lc hlc h hmem' hname
  exact ⟨restored, by rw [D.expr_eq D']; exact hr, hty⟩


end VerifyInductive
end Lean4Lean
