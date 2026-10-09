import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.CaseMotive
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.Injectivity

/-! The auxiliary-family header correspondence of a validated nested run.

For every lowered auxiliary family, the normalized signature's index count,
result level, header telescope and constructor names/universes agree with the
direct specialization of its certified container.  The constructor-type
restoration conjunct is taken as a hypothesis. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Syntactic specialization -/

theorem ContainerSpecialization.directFamily_fields
    {a : ContainerSpecialization} {U : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.specializedFamily U params = some direct) :
    direct.type = VExpr.wrapForalls params
        (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments) ∧
      direct.numIndices = a.source.numIndices ∧
      direct.resultLevel = a.source.resultLevel.inst a.levels := by
  unfold ContainerSpecialization.specializedFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, htype, ctors, _, he⟩ := H
  cases Option.some.inj he
  exact ⟨by rw [specializeType_eq_instantiateForallPrefix htype], rfl, rfl⟩


/-! ### Installed containers -/

private theorem install_type_lookup {base installed : VEnv} {block : VInductBlock}
    {value : VConstVal}
    (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.types) :
    installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact ((VEnv.addConstVals_le hc).trans <| VEnv.addEliminators_addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le).constants
      (VEnv.addConstVals_get ht hvalue)

/-- An installed container's families are present in the ambient environment,
are well-formed headers at the container's universe arity, and carry the
normalized type shape of their recorded index count and result level. -/
theorem _root_.Lean4Lean.VEnv.InstalledBelow.familyFacts {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∃ params, ∀ type ∈ decl.types,
      env.constants type.name = some type.toVConstant ∧
      type.uvars = decl.uvars ∧
      type.toVConstant.WF env ∧
      decl.TypeShape env params type := by
  cases H with
  | @intro _ _ base block installed hsource hformation hcompile _ hinstall hle =>
    have hbase : base ≤ env := (VInductBlock.install_base_le hinstall).trans hle
    have hparams : ∃ base', base' ≤ env ∧ VInductDecl.SourceParameterWF base' decl := by
      cases hformation with
      | ordinary hwf => exact ⟨base, hbase, hwf.sourceParameterWF⟩
      | nested hnested hle' =>
        cases hnested with
        | intro _ _ hparams _ _ _ _ => exact ⟨_, hle'.trans hbase, hparams⟩
    obtain ⟨base', hbase', params, _, _, hshapes, _, _⟩ := hparams
    obtain ⟨_, _, huvars, _, _, _, _, _, hheaders, _⟩ := hsource
    refine ⟨params, fun type htype => ⟨?_, huvars type htype,
      (hheaders type htype).mono hbase, typeShape_mono hbase' (hshapes type htype)⟩⟩
    apply hle.constants
    apply install_type_lookup hinstall
    rw [hcompile.types_eq]
    exact List.mem_map.mpr ⟨type, htype, rfl⟩

/-! ### Telescopes ending in sorts -/

/-- Definitionally equal forall telescopes ending in sorts have the same
length (forall/sort injectivity). -/
theorem VEnv.IsDefEqU.wrapForalls_sort_length {env : VEnv} {U : Nat}
    (henv : env.WF) :
    ∀ {Γ ds₁ ds₂ : List VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
      env.IsDefEqU U Γ (VExpr.wrapForalls ds₁ (.sort u))
        (VExpr.wrapForalls ds₂ (.sort v)) →
      ds₁.length = ds₂.length
  | _, [], [], _, _, _, _ => rfl
  | _, [], _ :: _, _, _, hΓ, H =>
    False.elim (Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv henv hΓ H)
  | _, _ :: _, [], _, _, hΓ, H =>
    False.elim (Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv henv hΓ H.symm)
  | Γ, d :: ds, _ :: ds', _, _, hΓ, H => by
    obtain ⟨⟨_, hd⟩, _, hb⟩ := Lean4Lean.VEnv.IsDefEqU.forallE_inv henv hΓ H
    have hctx : OnCtx (d :: Γ) (env.IsType U) := ⟨hΓ, _, hd.hasType.1⟩
    simpa using VEnv.IsDefEqU.wrapForalls_sort_length henv hctx ⟨_, hb⟩

/-- Applying a head whose type is a telescope ending in a sort to some
arguments, at a type which is again a telescope ending in a sort, consumes
exactly the difference of the two telescopes and preserves the sort level. -/
theorem VEnv.HasType.mkApps_sort_telescope {env : VEnv} {U : Nat} (henv : env.WF)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {E : List VExpr} {v : VLevel} :
    ∀ {f : VExpr} {D args : List VExpr} {u : VLevel},
      env.HasType U Γ f (VExpr.wrapForalls D (.sort u)) →
      env.HasType U Γ (VExpr.mkApps f args) (VExpr.wrapForalls E (.sort v)) →
      args.length + E.length = D.length ∧ u ≈ v
  | f, D, [], u, hf, ht => by
    have hdef := hf.uniqU henv hΓ ht
    exact ⟨by simpa using (VEnv.IsDefEqU.wrapForalls_sort_length henv hΓ hdef).symm,
      Lean4Lean.VEnv.IsDefEqU.wrapForalls_sort_level henv hΓ hdef⟩
  | f, D, arg :: args, u, hf, ht => by
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases D with
    | nil =>
      exact (Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv henv hΓ
        (hf.uniqU henv hΓ hfun)).elim
    | cons domain domains =>
      rcases Lean4Lean.VEnv.IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hfun) with
        ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change env.HasType U Γ (.app f arg)
        ((VExpr.wrapForalls domains (.sort u)).inst arg) at hfa'
      rw [VExpr.wrapForalls_inst] at hfa'
      have hrest := VEnv.HasType.mkApps_sort_telescope henv hΓ hfa' ht
      refine ⟨?_, hrest.2⟩
      have h1 := hrest.1
      simp only [VExpr.instDomains_length] at h1
      simp only [List.length_cons]
      omega

/-! ### One auxiliary family -/

/-- Header data of one auxiliary family: the normalized family `n`, modelled
on the lowered family `t`, which expands the generated family `g`, which is
the specialization `a` whose direct family is `d`. -/
theorem auxiliaryFamily_header
    {base envTypes : VEnv} {paramCtx params headerParams : List VExpr}
    {decl lowered : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {a : ContainerSpecialization} {g t n d : VInductiveType}
    (henv : envTypes.WF) (hle : base ≤ envTypes)
    (hev : SpecializationGenerates base envTypes paramCtx decl a g)
    (hexp : VInductDecl.NestedTypeExpansion base decl leaf g t)
    (hshape : lowered.TypeShape base headerParams t)
    (huvars : lowered.uvars = decl.uvars) (hnparams : lowered.nparams = decl.nparams)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hd : a.specializedFamily decl.uvars params = some d)
    (hni : n.numIndices = t.numIndices) (hrl : n.resultLevel ≈ t.resultLevel) :
    n.numIndices = d.numIndices ∧ n.resultLevel ≈ d.resultLevel ∧
    (∃ domains body level exprType, level ≈ n.resultLevel ∧
      envTypes.IsDefEq decl.uvars [] d.type
        (VExpr.wrapForalls domains body) exprType ∧
      envTypes.IsDefEq decl.uvars domains.reverse body (.sort level)
        (.sort (.succ level))) := by
  obtain ⟨hdType, hdIndices, hdLevel⟩ :=
    ContainerSpecialization.directFamily_fields hd
  obtain ⟨sp, hspLen, hspCtx, hspWF, htyping, hgType, _⟩ := hev.application
  generalize hR : VExpr.instantiateForallPrefix (a.source.type.instL a.levels)
    a.arguments = R at htyping hgType hdType
  have hRtype : envTypes.IsType decl.uvars sp.reverse R :=
    htyping.isType henv.ordered hspWF
  -- the lowered family's normalized header
  rcases hshape with ⟨Nt, own, after, idx, res, exprT, hN, htake₁, htake₂, _, hres⟩
  obtain ⟨rfl, hownLen⟩ := VExpr.takeForalls_rebuild htake₁
  obtain ⟨rfl, hidxLen⟩ := VExpr.takeForalls_rebuild htake₂
  rw [huvars] at hN hres
  replace hN := hN.mono hle
  replace hres := hres.mono hle
  have hspOwn : sp.length = own.length := by rw [hspLen, hownLen, hnparams]
  have hT : envTypes.IsDefEqU decl.uvars [] (VExpr.wrapForalls sp R)
      (VExpr.wrapForalls (own ++ idx) res) := by
    rw [VExpr.wrapForalls_append]
    exact (hgType.symm.trans henv trivial
      ((hexp.type.mono hle).trans henv trivial ⟨_, hN⟩))
  have hspWF' : OnCtx (sp.reverse ++ []) (envTypes.IsType decl.uvars) := by
    simpa using hspWF
  have hTtype : envTypes.IsType decl.uvars [] (VExpr.wrapForalls sp R) :=
    VEnv.IsType.wrapForalls hspWF' (by simpa using hRtype)
  have hres' : envTypes.IsDefEq decl.uvars (own ++ idx).reverse res
      (.sort t.resultLevel) (.sort (.succ t.resultLevel)) := by
    simpa [List.reverse_append] using hres
  obtain ⟨_, hT'⟩ := hT
  have hTsort := Lean4Lean.VEnv.IsDefEq.close_sort_header henv hTtype hT' hres'
  rw [VExpr.wrapForalls_append] at hTsort
  have hRsort : envTypes.IsDefEqU decl.uvars sp.reverse R
      (VExpr.wrapForalls idx (.sort t.resultLevel)) := by
    simpa using VEnv.IsDefEqU.wrapForalls_residual henv (ctx := []) trivial hspOwn hTsort
  -- the container's normalized header, specialised
  obtain ⟨cparams, hcfacts⟩ := hev.installed.familyFacts
  have hsrcMem : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  obtain ⟨hconst, hcuvars, hcWF, hcshape⟩ := hcfacts a.source hsrcMem
  rcases hcshape with ⟨Nc, ownc, afterc, idxc, resc, exprC, hNc, htakec₁, htakec₂, _, hresc⟩
  obtain ⟨rfl, hownc⟩ := VExpr.takeForalls_rebuild htakec₁
  obtain ⟨rfl, hidxc⟩ := VExpr.takeForalls_rebuild htakec₂
  have hcWF' : envTypes.IsType a.container.uvars [] a.source.type := by
    have h := hcWF.mono hle
    change envTypes.IsType a.source.uvars [] a.source.type at h
    rwa [hcuvars] at h
  have hresc' : envTypes.IsDefEq a.container.uvars (ownc ++ idxc).reverse resc
      (.sort a.source.resultLevel) (.sort (.succ a.source.resultLevel)) := by
    simpa [List.reverse_append] using hresc.mono hle
  have hNc' : envTypes.IsDefEq a.container.uvars [] a.source.type
      (VExpr.wrapForalls (ownc ++ idxc) resc) exprC := by
    rw [VExpr.wrapForalls_append]; exact hNc.mono hle
  have hcsort := Lean4Lean.VEnv.IsDefEq.close_sort_header henv hcWF' hNc' hresc'
  have hconstType : envTypes.HasType decl.uvars sp.reverse
      (.const a.source.name a.levels)
      (VExpr.wrapForalls ((ownc ++ idxc).map (·.instL a.levels))
        (.sort (a.source.resultLevel.inst a.levels))) := by
    have hc := Lean4Lean.VEnv.HasType.const (Γ := sp.reverse) (hle.constants hconst)
      hev.levelsWF (by rw [hev.levelsLength]; exact hcuvars.symm)
    have he := (hcsort.instL hev.levelsWF).weak0 henv.ordered (Γ := sp.reverse)
    simpa only [VExpr.instL_wrapForalls, VExpr.instL] using hc.defeqU_r henv hspWF he
  have happ := htyping.defeqU_r henv hspWF hRsort
  obtain ⟨hlen, hlevel⟩ := VEnv.HasType.mkApps_sort_telescope henv hspWF hconstType happ
  simp only [List.length_map, List.length_append] at hlen
  have hidxEq : t.numIndices = a.source.numIndices := by
    rw [← hidxLen, ← hidxc]
    rw [hev.argumentsLength, ← hownc] at hlen
    omega
  refine ⟨by rw [hni, hidxEq, hdIndices], ?_, ?_⟩
  · rw [hdLevel]; exact hrl.trans hlevel.symm
  · have hctx : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse sp.reverse :=
      VEnv.IsDefEqCtx.trans_empty henv hparams (hspCtx.symm henv.ordered)
    obtain ⟨w, hw⟩ := hRtype
    have hclose := VEnv.IsDefEqCtx.closeWrapForalls [] params.reverse sp.reverse
      (by simpa using hctx)
      (by rw [List.append_nil]; exact hw.defeqDFC henv.ordered (hctx.symm henv.ordered))
    simp only [List.reverse_reverse] at hclose
    have hfull : envTypes.IsDefEqU decl.uvars [] d.type
        (VExpr.wrapForalls (own ++ idx) res) := by
      rw [hdType]
      exact hclose.trans henv trivial ⟨_, hT'⟩
    obtain ⟨A, hA⟩ := hfull
    exact ⟨own ++ idx, res, t.resultLevel, A, hrl.symm, hA, hres'⟩

/-! ### The auxiliary suffix -/

/-- The `auxiliaryFamilies` relation of `NestedCompilationRestorationFacts`, for any
specialization list generated by lowering (`SpecializationGenerates`,
`NestedTypeExpansion`), given the restoration of the
auxiliary constructor types. -/
theorem auxiliaryFamilies_of_lowering
    {base envTypes : VEnv} {paramCtx params headerParams : List VExpr}
    {decl lowered : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {r : Restoration} {auxiliaries : List ContainerSpecialization}
    {generated targets normalized direct : List VInductiveType}
    (henv : envTypes.WF) (hle : base ≤ envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl leaf)
      generated targets)
    (HM : List.Forall₂ (fun n t : VInductiveType =>
        n.numIndices = t.numIndices ∧ n.resultLevel ≈ t.resultLevel ∧
        n.ctors.map VConstVal.name = t.ctors.map VConstVal.name)
      normalized targets)
    (Hshape : ∀ t ∈ targets, lowered.TypeShape base headerParams t)
    (huvars : lowered.uvars = decl.uvars) (hnparams : lowered.nparams = decl.nparams)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hctorUvars : ∀ n ∈ normalized, ∀ c ∈ n.ctors, c.uvars = decl.uvars)
    (hmapM : auxiliaries.mapM (fun a => a.specializedFamily decl.uvars params) = some direct)
    (Hrestores : List.Forall₂ (fun normalized family : VInductiveType =>
        List.Forall₂ (fun normalized ctor : VConstVal =>
          RestoresType r envTypes decl.uvars normalized.type ctor.type)
          normalized.ctors family.ctors)
      normalized direct) :
    List.Forall₂ (fun normalized family : VInductiveType =>
        normalized.numIndices = family.numIndices ∧
        normalized.resultLevel ≈ family.resultLevel ∧
        (∃ domains body level exprType, level ≈ normalized.resultLevel ∧
          envTypes.IsDefEq decl.uvars [] family.type
            (VExpr.wrapForalls domains body) exprType ∧
          envTypes.IsDefEq decl.uvars domains.reverse body (.sort level)
            (.sort (.succ level))) ∧
        List.Forall₂ (fun normalized ctor : VConstVal =>
          normalized.name = ctor.name ∧ normalized.uvars = ctor.uvars ∧
          RestoresType r envTypes decl.uvars normalized.type ctor.type)
          normalized.ctors family.ctors)
      normalized direct := by
  induction Haux generalizing targets normalized direct with
  | nil =>
    cases Hexp
    cases HM
    simp only [List.mapM_nil, pure, Option.some.injEq] at hmapM
    subst hmapM
    exact .nil
  | @cons a g auxs gens hev _ ih =>
    cases Hexp with
    | @cons _ t _ ts hexp hexps =>
    cases HM with
    | @cons n _ ns _ hM hMs =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hmapM
    obtain ⟨d, hd, ds, hds, rfl⟩ := hmapM
    cases Hrestores with
    | cons hR hRs =>
    refine .cons ?_ (ih hexps hMs (fun t ht => Hshape t (List.mem_cons_of_mem _ ht))
      (fun n hn => hctorUvars n (List.mem_cons_of_mem _ hn)) hds hRs)
    obtain ⟨h1, h2, h3⟩ := auxiliaryFamily_header henv hle hev hexp
      (Hshape t List.mem_cons_self) huvars hnparams hparams hd hM.1 hM.2.1
    refine ⟨h1, h2, h3, ?_⟩
    obtain ⟨d', hd', hshape⟩ := a.directFamily_isSome decl.uvars params
      hev.familyForallPrefix (fun _ h => hev.ctorForallPrefix h)
    rw [hd] at hd'
    cases hd'
    have hnames : n.ctors.map VConstVal.name = d.ctors.map VConstVal.name := by
      rw [hM.2.2, nestedConstructorExpansions_names hexp.constructors,
        hev.generatedCtorNames, hshape.ctorNames]
    refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem
      (Lean4Lean.List.Forall₂.and (forall₂_of_map_eq hnames) hR))
    rintro nc c ⟨⟨hname, hRT⟩, hnc, hc⟩
    exact ⟨hname, (hctorUvars n List.mem_cons_self nc hnc).trans
      (hshape.ctorUvars c hc).symm, hRT⟩

end VerifyInductive
end Lean4Lean
