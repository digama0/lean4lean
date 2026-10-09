import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleArity
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjStaticWF
import Lean4Lean.Theory.Typing.EnvTables.Arity

/-! # Field counts of compiled constructors, from soundness of the header environment

`CaseCompilationData.ctor_arity_sem`: the field count of a constructor of a compilation's normalized
signature, plus its parameter count, is the syntactic arity of the source (or container)
constructor type. It uses the soundness, in the model of a later environment `envF`, of an
environment containing the compilation's headers (`Model.tele_arity`): the restored normalized
constructor type and the source constructor type are definitionally equal telescopes ending in
applications of the family, which is rigid in `envF`. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

/-- The constant at the end of a forall telescope. -/
def EndHead (e : VExpr) (h : Name) : Prop := ∃ ls, e.forallResult.getAppFnArgs.1 = .const h ls

theorem forallResult_tele (e : VExpr) :
    ∃ doms, e = VExpr.wrapForalls doms e.forallResult ∧ doms.length = e.forallArity := by
  induction e with
  | forallE d b _ ih =>
    obtain ⟨doms, he, hl⟩ := ih
    exact ⟨d :: doms, by
      change VExpr.forallE d b = VExpr.forallE d (VExpr.wrapForalls doms b.forallResult)
      rw [← he], by simp [VExpr.forallArity, hl]⟩
  | _ => exact ⟨[], rfl, rfl⟩

theorem EndHead.form {e : VExpr} {h : Name} (H : EndHead e h) :
    ∃ doms ls args, e = VExpr.wrapForalls doms (VExpr.mkApps (.const h ls) args) ∧
      doms.length = e.forallArity := by
  obtain ⟨ls, hh⟩ := H
  obtain ⟨doms, he, hl⟩ := forallResult_tele e
  refine ⟨doms, ls, e.forallResult.getAppFnArgs.2, ?_, hl⟩
  conv => lhs; rw [he]
  congr 1
  rw [← hh, VExpr.mkApps_getAppFnArgs]

theorem EndHead.wrapForalls {ds : List VExpr} {b : VExpr} {h : Name} :
    EndHead (VExpr.wrapForalls ds b) h ↔ EndHead b h := by
  simp [EndHead, VExpr.forallResult_wrapForalls]

theorem EndHead.of_mkApps {h : Name} {ls : List VLevel} {args : List VExpr} :
    EndHead (VExpr.mkApps (.const h ls) args) h := by
  refine ⟨ls, ?_⟩
  rw [VExpr.forallResult_of_head (by rw [VExpr.getAppFnArgs_mkApps_const])]
  rw [VExpr.getAppFnArgs_mkApps_const]

theorem EndHead.of_notForall {e : VExpr} {h : Name} (hf : e.forallResult = e) (H : EndHead e h) :
    ∃ ls args, e = VExpr.mkApps (.const h ls) args := by
  obtain ⟨ls, hh⟩ := H
  rw [hf] at hh
  refine ⟨ls, e.getAppFnArgs.2, ?_⟩
  conv => lhs; rw [← VExpr.mkApps_getAppFnArgs e]
  rw [hh]

theorem EndHead.subst {h : Name} {e : VExpr} : ∀ {σ : VExpr.Subst}, EndHead e h →
    EndHead (e.subst σ) h := by
  induction e with
  | forallE A B _ ih =>
    intro σ H
    exact ih (σ := σ.lift) H
  | _ =>
    intro σ H
    obtain ⟨ls, args, he⟩ := H.of_notForall rfl
    rw [he, VExpr.subst_mkApps]
    exact .of_mkApps

theorem EndHead.instL {h : Name} {e : VExpr} {us : List VLevel} (H : EndHead e h) :
    EndHead (e.instL us) h := by
  obtain ⟨doms, ls, args, he, -⟩ := H.form
  rw [he, VExpr.instL_wrapForalls, EndHead.wrapForalls, VExpr.instL_mkApps]
  exact .of_mkApps

theorem EndHead.takeForalls {h : Name} : ∀ {k : Nat} {e body : VExpr} {ds : List VExpr},
    e.takeForalls k = some (ds, body) → EndHead e h → EndHead body h
  | 0, e, body, ds, ht, H => by cases Option.some.inj ht; exact H
  | k + 1, .forallE d b, body, ds, ht, H => by
    cases hb : b.takeForalls k with
    | none => simp [VExpr.takeForalls, hb] at ht
    | some out =>
      rw [VExpr.takeForalls, hb] at ht
      cases Option.some.inj ht
      exact EndHead.takeForalls hb H
  | _ + 1, .bvar .., _, _, ht, _ | _ + 1, .sort .., _, _, ht, _ | _ + 1, .const .., _, _, ht, _
  | _ + 1, .elim .., _, _, ht, _ | _ + 1, .app .., _, _, ht, _ | _ + 1, .lam .., _, _, ht, _
  | _ + 1, .proj .., _, _, ht, _ => by simp [VExpr.takeForalls] at ht

theorem EndHead.specialize {h : Name} {type t : VExpr} {args : List VExpr}
    (H : EndHead type h) (hs : InductiveSignature.specializeType type args = some t) :
    EndHead t h := by
  simp only [InductiveSignature.specializeType, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hs
  obtain ⟨⟨ds, body⟩, ht, rfl⟩ := hs
  exact (H.takeForalls ht).subst

theorem EndHead.restore {h : Name} {r : Restoration} {e e' : VExpr} (H : EndHead e h)
    (hr : r.expr e = some e') : EndHead e' (r.headName h) := by
  obtain ⟨doms, ls, args, he, -⟩ := H.form
  rw [he] at hr
  obtain ⟨ds', b', -, hb, rfl⟩ := Restoration.expr_wrapForalls_parts hr
  obtain ⟨args', rfl⟩ := Restoration.const_mkApps_exact hb
  exact EndHead.wrapForalls.2 .of_mkApps

theorem EndHead.forallArity_teleArity {h : Name} {e : VExpr} (H : EndHead e h) :
    EnvTables.teleArity e = some e.forallArity := by
  obtain ⟨ls, hh⟩ := H
  exact EnvTables.teleArity_of_forallResult hh

/-- **Arity of rigid-ended telescopes**, by end heads. -/
theorem Model.tele_arity_end {envF E : VEnv} (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ)
    {e e' : VExpr} {h h' : Name} {U : Nat} (H : EndHead e h) (H' : EndHead e' h')
    (hrig : envF.Rigid h) (hrig' : envF.Rigid h') (hd : E.IsDefEqU U [] e e') :
    e.forallArity = e'.forallArity := by
  obtain ⟨T, hd⟩ := hd
  obtain ⟨doms, ls, args, he, hl⟩ := H.form
  obtain ⟨doms', ls', args', he', hl'⟩ := H'.form
  rw [he, he'] at hd
  rw [← hl, ← hl']
  exact tele_arity hE hEF hsnd hrig hrig' hd

theorem directFamily_name {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {fam : VInductiveType} (H : a.specializedFamily uvars params = some fam) : fam.name = a.auxiliary := by
  unfold ContainerSpecialization.specializedFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, -, H⟩
    cases H
    rfl

/-- **Field counts of a compilation's equations against the source constructor arities**, from
soundness of an environment `E` containing the compilation's headers. -/
theorem CaseCompilationData.ctor_arity_sem {envF base E : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock}
    (hdata : CaseCompilationData base src exp s aux block)
    (hfresh : RecursorNamesFresh base src exp aux)
    (hprior : ContainersInstalled base aux)
    (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → Model.SoundTypedIn envF E U Δ) (hle : base ≤ E)
    (htypes : ∀ t ∈ src.types, E.constants t.name = some t.toVConstant)
    (index : Fin s.constructors.size)
    (hrigF : envF.Rigid ((compilationRestoration src aux).headName
      s.families[s.constructors[index].owner].name)) :
    (∃ F ∈ src.types, ∃ c ∈ F.ctors, s.constructors[index].name = c.name ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.params.length + s.constructors[index].fields.length = c.type.forallArity) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, s.constructors[index].name = a.constructorName c ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.constructors[index].fields.length + a.arguments.length = c.type.forallArity) := by
  obtain ⟨envTypes, direct, hT, hdirect, _, hfamilies⟩ := hdata.correspondence
  have hTE : envTypes ≤ E := EnvTables.addConstVals_le_of hT hle (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci; exact htypes t ht)
  obtain ⟨fam, hfam, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨sc, hsc, hname, _, restored, hres, hdefeq⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ (s.declarationCtor_family index)
  have hdefeq' : E.IsDefEqU src.uvars [] restored sc.type :=
    let ⟨T, h⟩ := hdefeq; ⟨T, h.mono hTE⟩
  have hnormE : EndHead (s.declarationCtor index).type
      s.families[s.constructors[index].owner].name := by
    simp only [declarationCtor, constructorType, familyApp]
    exact EndHead.wrapForalls.2 .of_mkApps
  have hrestE := hnormE.restore hres
  have hrigR := hrigF
  have hfn : s.families[s.constructors[index].owner].name = fam.name := hrel.name
  have hnorm : EnvTables.teleArity (s.declarationCtor index).type =
      some (s.params.length + s.constructors[index].fields.length) := by
    have := EnvTables.teleArity_ctorShape (doms := s.params ++ s.fieldTypes s.constructors[index])
      (c := s.families[s.constructors[index].owner].name) (ls := VLevel.params s.uvars)
      (args := vars s.params.length s.constructors[index].fields.length ++
        s.constructors[index].indices)
    simpa [declarationCtor, constructorType, familyApp, fieldTypes] using this
  have hrestA := EnvTables.teleArity_restore hnorm hres
  rw [hrestE.forallArity_teleArity, Option.some.injEq] at hrestA
  have hname' : s.constructors[index].name = sc.name := hname
  rcases List.mem_append.mp hfam with hsrc | hdir
  · left
    refine ⟨fam, hsrc, sc, hsc, hname', ?_, ?_⟩
    · rw [hname']
      exact hdata.headName_source hfresh (List.mem_flatMap.mpr ⟨fam, hsrc,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨sc, hsc, rfl⟩)⟩)
    · obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
      obtain ⟨doms, result, heq, _, _, hhead, harity⟩ := (hraw fam hsrc sc hsc).forallArity
      have hscE : EndHead sc.type fam.name := by
        rw [heq, EndHead.wrapForalls]
        exact ⟨_, by rw [VExpr.forallResult_of_head hhead]; exact hhead⟩
      have hrigS : envF.Rigid fam.name := by
        rw [hfn, hdata.headName_source hfresh (List.mem_flatMap.mpr ⟨fam, hsrc, List.mem_cons_self⟩)] at hrigF
        exact hrigF
      rw [← hrestA]
      exact Model.tele_arity_end hE hEF hsnd hrestE hscE hrigR hrigS hdefeq'
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) fam hdir
    obtain ⟨c, hc, t, hspec, hdcn, hdct⟩ := EnvTables.directFamily_ctor hdf hsc
    refine ⟨a, ha, c, hc, hname'.trans hdcn, ?_, ?_⟩
    · rw [hname', hdcn]
      exact hdata.headName_auxiliary_constructor ha hc
    · obtain ⟨_, ls, hres'⟩ := (hprior.container_ctor a ha c hc)
      have hcA := EnvTables.teleArity_instL (EnvTables.teleArity_of_forallResult hres') a.levels
      obtain ⟨hk, htA⟩ := EnvTables.teleArity_specializeType hcA hspec
      have hscA : EnvTables.teleArity sc.type = some (s.params.length + (c.type.forallArity -
          a.arguments.length)) := by
        rw [hdct]; exact EnvTables.teleArity_wrapForalls htA
      have hcE : EndHead (c.type.instL a.levels) a.source.name := EndHead.instL ⟨ls, hres'⟩
      have hscE : EndHead sc.type a.source.name := by
        rw [hdct, EndHead.wrapForalls]; exact hcE.specialize hspec
      rw [hscE.forallArity_teleArity, Option.some.injEq] at hscA
      have hhd : (compilationRestoration src aux).headName a.auxiliary = a.source.name :=
        Restoration.headName_of_mem (spec := HeadSpecialization.mk a.auxiliary src.uvars
          src.nparams a.source.name a.levels a.arguments) hdata.restorationScoped
          (List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩)
      have hrigA : envF.Rigid a.source.name := by
        rw [hfn, directFamily_name hdf, hhd] at hrigF
        exact hrigF
      have := Model.tele_arity_end hE hEF hsnd hrestE hscE hrigR hrigA hdefeq'
      omega

/-- The field count of a source-constructor equation. -/
theorem CaseCompilationData.source_arity_sem {envF base E : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hfresh : RecursorNamesFresh base src exp aux)
    (hprior : ContainersInstalled base aux) (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → Model.SoundTypedIn envF E U Δ) (hle : base ≤ E)
    (htypes : ∀ t ∈ src.types, E.constants t.name = some t.toVConstant)
    (j : Fin s.constructors.size)
    (hrigF : envF.Rigid ((compilationRestoration src aux).headName
      s.families[s.constructors[j].owner].name)) {F : VInductiveType} (hF : F ∈ src.types)
    {c : VConstVal} (hc : c ∈ F.ctors) (hcn : c.name = s.constructors[j].name) :
    s.params.length + s.constructors[j].fields.length = c.type.forallArity := by
  have hnd := hdata.sourceWF.2.1
  have hcn' : c.name ∈ familyNames src.types :=
    List.mem_flatMap.mpr ⟨F, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  rcases CaseCompilationData.ctor_arity_sem hdata hfresh hprior hE hEF hsnd hle htypes j hrigF with
    ⟨F', hF', c', hc', hn', _, harity⟩ | ⟨a, ha, c', hc', hn', _, _⟩
  · have hcc : c' = c := by
      have hnd' := (List.nodup_append.mp hnd).2.1
      exact List.eq_of_mem_of_nodup_map hnd' (List.mem_flatMap.mpr ⟨F', hF', hc'⟩)
        (List.mem_flatMap.mpr ⟨F, hF, hc⟩) (hn'.symm.trans hcn.symm)
    rw [← hcc]; exact harity
  · exfalso
    exact hdata.source_head_disjoint hcn'
      (List.mem_map.mpr ⟨_, EnvTables.auxCtor_head_mem (src := src) ha hc',
        (hn'.symm.trans hcn.symm)⟩)

/-- The field count of a container-constructor equation. -/
theorem CaseCompilationData.container_arity_sem {envF base E : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hfresh : RecursorNamesFresh base src exp aux)
    (hprior : ContainersInstalled base aux) (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → Model.SoundTypedIn envF E U Δ) (hle : base ≤ E)
    (htypes : ∀ t ∈ src.types, E.constants t.name = some t.toVConstant)
    (j : Fin s.constructors.size)
    (hrigF : envF.Rigid ((compilationRestoration src aux).headName
      s.families[s.constructors[j].owner].name)) {a : ContainerSpecialization} (ha : a ∈ aux)
    {c : VConstVal} (hc : c ∈ a.source.ctors) (hcn : s.constructors[j].name = a.constructorName c) :
    s.constructors[j].fields.length + a.arguments.length = c.type.forallArity := by
  rcases CaseCompilationData.ctor_arity_sem hdata hfresh hprior hE hEF hsnd hle htypes j hrigF with
    ⟨F', hF', c', hc', hn', _, _⟩ | ⟨a', ha', c', hc', hn', _, harity⟩
  · exfalso
    have hcn' : c'.name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨F', hF', List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)⟩
    exact hdata.source_head_disjoint hcn'
      (List.mem_map.mpr ⟨_, EnvTables.auxCtor_head_mem (src := src) ha hc, (hcn.symm.trans hn')⟩)
  · have heq := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1
      (EnvTables.auxCtor_head_mem (src := src) ha' hc')
      (EnvTables.auxCtor_head_mem (src := src) ha hc)
      (hn'.symm.trans hcn)
    simp only [HeadSpecialization.mk.injEq] at heq
    obtain ⟨_, _, _, htarget, _, hargs⟩ := heq
    rw [← hargs]
    have h1 := (hprior.container_ctor a' ha' c' hc').1
    have h2 := (hprior.container_ctor a ha c hc).1
    rw [htarget, h2] at h1
    have : c'.type = c.type := congrArg VConstant.type (Option.some.inj h1).symm
    rw [← this]; exact harity

end VEnv
end Lean4Lean
