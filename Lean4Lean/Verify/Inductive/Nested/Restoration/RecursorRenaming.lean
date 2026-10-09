import Lean4Lean.Verify.Inductive.Nested.Install.RecursorTranslations
import Lean4Lean.Std.Basic

/-! # Renamed auxiliary recursor names and the restorable names

The restored auxiliary recursors are installed under the names
`Main.rec_k = (Main.str "rec").appendIndexAfter k` (`mkAuxRecNameMap`,
`compilationRestoration`). Nothing in the run or in the source checks
excludes that such a name coincides with an auxiliary constructor name
`_nested.i.suffix` (the first source family may be named `_nested.i.x` and
have no constructors, and a container may have a constructor `J.x.rec_k`).
In that case the restorable name is installed in every recursor environment
of the nested installation (as the restored recursor), so freshness of *all*
restorable names there fails.

This file proves what holds without any naming hypothesis:

* `NestedRun.recursorVEnv_restorableNames_fresh_of_not_renamed`:
  every restorable name which is not a renamed recursor name is absent from
  the abstract recursor environment of any `RestoredBlockBase`.
* `InductiveSignature.compilationRestoration_recursors_snd_str`: every renamed
  recursor name is a string extension of the first source family name.
-/

namespace Lean.Expr

open Lean4Lean

/-! ### Input-side avoidance at head occurrences -/

/-- `TrailingArgsAvoid heads names np e`: in `e`, every literal and every argument
after the first `np` of an application spine headed by a constant of `heads`
(a *head occurrence*; `restoreNestedNode` copies these arguments verbatim) avoids
`names`. Parameter arguments and everything outside head occurrences are
unconstrained. -/
inductive TrailingArgsAvoid (heads names : List Name) (np : Nat) : Expr → Prop
  | bvar (i : Nat) : TrailingArgsAvoid heads names np (.bvar i)
  | fvar (fv : FVarId) : TrailingArgsAvoid heads names np (.fvar fv)
  | mvar (mv : MVarId) : TrailingArgsAvoid heads names np (.mvar mv)
  | sort (u : Level) : TrailingArgsAvoid heads names np (.sort u)
  | const (c : Name) (us : List Level) : TrailingArgsAvoid heads names np (.const c us)
  | lit (l : Literal) : (Expr.lit l).AvoidsConsts names →
      TrailingArgsAvoid heads names np (.lit l)
  | app {f a : Expr} : TrailingArgsAvoid heads names np f → TrailingArgsAvoid heads names np a →
      (∀ c us, (Expr.app f a).getAppFn = .const c us → c ∈ heads →
        ∀ x ∈ ((Expr.app f a).getAppArgsList).drop np, x.AvoidsConsts names) →
      TrailingArgsAvoid heads names np (.app f a)
  | lam {n : Name} {t b : Expr} {bi : BinderInfo} :
      TrailingArgsAvoid heads names np t → TrailingArgsAvoid heads names np b →
      TrailingArgsAvoid heads names np (.lam n t b bi)
  | forallE {n : Name} {t b : Expr} {bi : BinderInfo} :
      TrailingArgsAvoid heads names np t → TrailingArgsAvoid heads names np b →
      TrailingArgsAvoid heads names np (.forallE n t b bi)
  | letE {n : Name} {t v b : Expr} {nd : Bool} :
      TrailingArgsAvoid heads names np t → TrailingArgsAvoid heads names np v →
      TrailingArgsAvoid heads names np b →
      TrailingArgsAvoid heads names np (.letE n t v b nd)
  | mdata {m : MData} {e : Expr} : TrailingArgsAvoid heads names np e →
      TrailingArgsAvoid heads names np (.mdata m e)
  | proj {s : Name} {i : Nat} {e : Expr} : TrailingArgsAvoid heads names np e →
      TrailingArgsAvoid heads names np (.proj s i e)

/-- `LamPrefixAvoids names n e`: the first `n` binder domains of the lambda
telescope `e` avoid `names`. -/
inductive LamPrefixAvoids (names : List Name) : Nat → Expr → Prop
  | zero (e : Expr) : LamPrefixAvoids names 0 e
  | succ {n : Nat} {x : Name} {d b : Expr} {bi : BinderInfo} :
      d.AvoidsConsts names → LamPrefixAvoids names n b →
      LamPrefixAvoids names (n + 1) (.lam x d b bi)

/-- Avoidance of a list of names follows from avoidance of two lists covering it. -/
theorem AvoidsConsts.of_cover {L L₁ L₂ : List Name}
    (hcover : ∀ n ∈ L, n ∈ L₁ ∨ n ∈ L₂) {e : Expr}
    (h₁ : e.AvoidsConsts L₁) (h₂ : e.AvoidsConsts L₂) : e.AvoidsConsts L := by
  induction h₁ with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const c us hc =>
    cases h₂ with
    | const _ _ hc₂ =>
      exact .const _ _ fun hn => (hcover c hn).elim hc hc₂
  | app _ _ _ _ ihf iha =>
    cases h₂ with | app _ _ hf ha => exact .app _ _ (ihf hf) (iha ha)
  | lam _ _ _ _ _ _ ihd ihb =>
    cases h₂ with | lam _ _ _ _ hd hb => exact .lam _ _ _ _ (ihd hd) (ihb hb)
  | forallE _ _ _ _ _ _ ihd ihb =>
    cases h₂ with | forallE _ _ _ _ hd hb => exact .forallE _ _ _ _ (ihd hd) (ihb hb)
  | letE _ _ _ _ _ _ _ _ iht ihv ihb =>
    cases h₂ with
    | letE _ _ _ _ _ ht hv hb => exact .letE _ _ _ _ _ (iht ht) (ihv hv) (ihb hb)
  | lit _ _ ih => cases h₂ with | lit _ h => exact .lit _ (ih h)
  | mdata _ _ _ ih => cases h₂ with | mdata _ _ h => exact .mdata _ _ (ih h)
  | proj _ _ _ _ ih => cases h₂ with | proj _ _ _ h => exact .proj _ _ _ (ih h)

theorem AvoidsConsts.mono {L L' : List Name} (hsub : ∀ n ∈ L', n ∈ L) {e : Expr}
    (h : e.AvoidsConsts L) : e.AvoidsConsts L' :=
  AvoidsConsts.of_cover (L₂ := L) (fun n hn => .inl (hsub n hn)) h h

private theorem instantiate1'_fvar_bvar (i k : Nat) (fv : FVarId) :
    (∃ j, instantiate1' (.bvar i) (.fvar fv) k = .bvar j) ∨
      instantiate1' (.bvar i) (.fvar fv) k = .fvar fv := by
  simp only [instantiate1']
  split
  · exact .inl ⟨i, rfl⟩
  · split
    · right; simp [liftLooseBVars']
    · exact .inl ⟨_, rfl⟩

theorem getAppFn_instantiate1'_fvar (fv : FVarId) :
    ∀ (e : Expr) (k : Nat),
      (instantiate1' e (.fvar fv) k).getAppFn = instantiate1' e.getAppFn (.fvar fv) k
  | .app f _, k => by
    simp only [instantiate1', getAppFn]
    exact getAppFn_instantiate1'_fvar fv f k
  | .bvar i, k => by
    rcases instantiate1'_fvar_bvar i k fv with ⟨j, h⟩ | h <;> simp [getAppFn, h]
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem getAppArgsList_instantiate1'_fvar (fv : FVarId) :
    ∀ (e : Expr) (k : Nat),
      (instantiate1' e (.fvar fv) k).getAppArgsList =
        e.getAppArgsList.map (instantiate1' · (.fvar fv) k)
  | .app f a, k => by
    simp only [instantiate1', getAppArgsList_app, List.map_append, List.map_cons,
      List.map_nil]
    rw [getAppArgsList_instantiate1'_fvar fv f k]
  | .bvar i, k => by
    rcases instantiate1'_fvar_bvar i k fv with ⟨j, h⟩ | h <;> simp [getAppArgsList, h]
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem eq_const_of_instantiate1'_fvar {fv : FVarId} {k : Nat} {c : Name} {us : List Level} :
    ∀ {x : Expr}, instantiate1' x (.fvar fv) k = .const c us → x = .const c us
  | .bvar i, h => by
    rcases instantiate1'_fvar_bvar i k fv with ⟨j, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | .const _ _, h => h
  | .fvar _, h | .mvar _, h | .sort _, h | .lit _, h => by cases h
  | .app .., h | .lam .., h | .forallE .., h | .letE .., h | .mdata .., h | .proj .., h => by
    simp [instantiate1'] at h

theorem TrailingArgsAvoid.instantiate1'_fvar {heads names : List Name} {np : Nat} {e : Expr}
    (H : e.TrailingArgsAvoid heads names np) (fv : FVarId) (k : Nat) :
    (instantiate1' e (.fvar fv) k).TrailingArgsAvoid heads names np := by
  induction H generalizing k with
  | bvar i =>
    rcases instantiate1'_fvar_bvar i k fv with ⟨j, h⟩ | h <;> rw [h]
    · exact .bvar _
    · exact .fvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit _ h => exact .lit _ h
  | @app f a _ _ htrail ihf iha =>
    refine .app (ihf k) (iha k) ?_
    intro c us hfn hc x hx
    have hfn' : (Expr.app f a).getAppFn = .const c us := by
      have h := getAppFn_instantiate1'_fvar fv (.app f a) k
      simp only [instantiate1'] at h
      rw [h] at hfn
      exact eq_const_of_instantiate1'_fvar hfn
    have hargs := getAppArgsList_instantiate1'_fvar fv (.app f a) k
    simp only [instantiate1'] at hargs
    rw [hargs, ← List.map_drop] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (htrail c us hfn' hc y hy).instantiate1'_fvar fv k
  | lam _ _ ihd ihb => exact .lam (ihd k) (ihb (k + 1))
  | forallE _ _ ihd ihb => exact .forallE (ihd k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht k) (ihv k) (ihb (k + 1))
  | mdata _ ih => exact .mdata (ih k)
  | proj _ ih => exact .proj (ih k)

theorem TrailingArgsAvoid.instantiateRevList_fvars {heads names : List Name} {np : Nat}
    {e : Expr} (H : e.TrailingArgsAvoid heads names np) (fvs : List FVarId) (k : Nat) :
    (e.instantiateRevList (fvs.map .fvar) k).TrailingArgsAvoid heads names np := by
  induction fvs with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [List.map_cons, instantiateRevList]
    exact ih.instantiate1'_fvar fv k

/-- The residual of a lambda telescope inherits `TrailingArgsAvoid`. -/
theorem TrailingArgsAvoid.lambdaTelescope {heads names : List Name} {np : Nat}
    {e suffix : Expr} {n : Nat} (Htel : Lean4Lean.VerifyInductive.Expr.LambdaTelescope e n suffix)
    (H : e.TrailingArgsAvoid heads names np) : suffix.TrailingArgsAvoid heads names np := by
  induction Htel with
  | nil => exact H
  | cons _ ih => cases H with | lam _ hb => exact ih hb

/-- At a head occurrence, the trailing arguments avoid the names. -/
theorem TrailingArgsAvoid.trail {heads names : List Name} {np : Nat} {e : Expr}
    (H : e.TrailingArgsAvoid heads names np) {c : Name} {us : List Level}
    (hfn : e.getAppFn = .const c us) (hc : c ∈ heads) :
    ∀ x ∈ e.getAppArgsList.drop np, x.AvoidsConsts names := by
  cases H with
  | app _ _ h => exact h c us hfn hc
  | _ => intro x hx; simp [getAppArgsList] at hx

end Lean.Expr

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The restorable names of any restoration table of a run are restorable
names of any other one: both tables are keyed by the same auxiliary families
(`familyKey`, `familyLookup`) and constructors (`ctorInstalled`,
`ctorLookup`) of the lowered environment. -/
theorem RestorationTablesAgree.restorableNames_subset
    {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}
    {auxiliaries auxiliaries' : List ContainerSpecialization}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    (D' : RestorationTablesAgree decl auxiliaries' result env auxRec Us₀) :
    ∀ n ∈ (compilationRestoration decl auxiliaries).restorableNames,
      n ∈ (compilationRestoration decl auxiliaries').restorableNames := by
  have hfamily : ∀ a ∈ auxiliaries, ∃ a' ∈ auxiliaries', a'.auxiliary = a.auxiliary := by
    intro a ha
    obtain ⟨nested, hnested⟩ := D.familyLookup a ha
    obtain ⟨a', ha', heq, -⟩ := D'.familyKey _ _ hnested
    exact ⟨a', ha', heq⟩
  intro n hn
  simp only [Restoration.restorableNames, compilationRestoration_heads_auxiliary,
    compilationRestoration_recursors_fst, List.mem_append, List.mem_flatMap,
    List.mem_map] at hn ⊢
  rcases hn with ⟨a, ha, hn⟩ | ⟨a, ha, rfl⟩
  · obtain ⟨a', ha', heq⟩ := hfamily a ha
    simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact .inl ⟨a', ha', by simp [ContainerSpecialization.headNames, heq]⟩
    · obtain ⟨info, hfind, hinduct⟩ := D.ctorInstalled a ha ctor hctor
      obtain ⟨ctor', hctor', hname⟩ :=
        D'.ctorLookup _ info hfind a' ha' (hinduct.trans heq.symm)
      refine .inl ⟨a', ha', ?_⟩
      simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map]
      exact .inr ⟨ctor', hctor', hname.symm⟩
  · obtain ⟨a', ha', heq⟩ := hfamily a ha
    exact .inr ⟨a', ha', by rw [heq]⟩

/-- The lowered auxiliary recursor names of any restoration table of a run
are those of any other one. -/
theorem RestorationTablesAgree.recursors_fst_subset
    {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}
    {auxiliaries auxiliaries' : List ContainerSpecialization}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    (D' : RestorationTablesAgree decl auxiliaries' result env auxRec Us₀) :
    ∀ c ∈ (compilationRestoration decl auxiliaries).recursors.map Prod.fst,
      c ∈ (compilationRestoration decl auxiliaries').recursors.map Prod.fst := by
  intro c hc
  rw [compilationRestoration_recursors_fst] at hc ⊢
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  obtain ⟨nested, hnested⟩ := D.familyLookup a ha
  obtain ⟨a', ha', heq, -⟩ := D'.familyKey _ _ hnested
  exact List.mem_map.mpr ⟨a', ha', by rw [heq]⟩

theorem _root_.Lean4Lean.InductiveSignature.Restoration.recursorName_cases (r : Restoration) (c : Name) :
    r.recursorName c = c ∨ ∃ p ∈ r.recursors, p.1 = c ∧ r.recursorName c = p.2 := by
  unfold Restoration.recursorName
  cases h : r.recursors.find? (fun pair => pair.1 == c) with
  | none => exact .inl rfl
  | some p =>
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    exact .inr ⟨p, hmem, by simpa using hp, rfl⟩

/-- A lowered recursor name of a restoration table is renamed to one of the
table's renamed names. -/
theorem _root_.Lean4Lean.InductiveSignature.Restoration.recursorName_mem_snd
    (r : Restoration) {c : Name} (hc : c ∈ r.recursors.map Prod.fst) :
    r.recursorName c ∈ r.recursors.map Prod.snd := by
  have hsome : (r.recursors.find? (fun pair => pair.1 == c)).isSome := by
    rw [List.find?_isSome]
    obtain ⟨q, hq, hqc⟩ := List.mem_map.mp hc
    exact ⟨q, hq, by simp [hqc]⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  have hrn : r.recursorName c = q.2 := by
    unfold Restoration.recursorName
    rw [hq]
  rw [hrn]
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some hq)

/-- **Freshness of the non-renamed restorable names in a restored block.**
For any `RestoredBlockBase` of a validated nested run and any
restoration table of the run, every restorable name (auxiliary family and
constructor names and lowered auxiliary recursor names) that is not one of
the table's renamed recursor names `Main.rec_k` is absent from its abstract
recursor environment: it is fresh in the source constructor
environment (`restorableNames_fresh_ctors`), the restored source recursors
keep their lowered names `T.rec` (distinct from the auxiliary names by the
lowered declaration's name uniqueness), and the remaining installed names are
renamed recursor names. No hypothesis on names is needed. -/
theorem NestedRun.recursorVEnv_restorableNames_fresh_of_not_renamed
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
      C.recursorVEnv.constants n = none := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D', -, -⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, hheadNames, -, -, -, hscoped, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.install.recursorsAdded.abstract
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D' hscoped hwf
  let r' := compilationRestoration sourceDecl aux'
  intro n hn hnRen
  have hn' : n ∈ r'.restorableNames := D.restorableNames_subset D' n hn
  -- no lowered auxiliary recursor name of `r'` is renamed to `n`
  have hnot : ∀ c ∈ r'.recursors.map Prod.fst, r'.recursorName c ≠ n := by
    intro c hc hcn
    have hsame : r'.recursorName c =
        (compilationRestoration sourceDecl auxiliaries).recursorName c := by
      rw [D'.recursorName, D.recursorName]
    have hc' := D'.recursors_fst_subset D c hc
    exact hnRen (hcn ▸ hsame ▸ Restoration.recursorName_mem_snd _ hc')
  cases hc : C.recursorVEnv.constants n with
  | none => rfl
  | some ci =>
  exfalso
  rcases VEnv.addConstVals_lookup_cases hrecAdded hc with hbase | ⟨entry, hentry, hname, -⟩
  · simp only [VEnv.addEliminators_constants, VEnv.addProjections_constants] at hbase
    rw [hfreshCtors n hn'] at hbase
    cases hbase
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hentry
  obtain ⟨owner, -, s, t, Hstep, -, hrec, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hinfos e he
  -- the restored recursor name
  have hename : e.2.name = r'.recursorName
      (E.lowered.recursors.canonicalGeneration.recursorName owner) := by
    simp only [Restoration.recursor, Option.pure_def, Option.bind_eq_bind] at hrec
    cases hty : r'.expr
        (E.lowered.recursors.canonicalGeneration.recursor owner).type with
    | none => simp [r', hty] at hrec
    | some ty =>
      simp only [r', hty, Option.bind_some, Option.some.injEq] at hrec
      rw [← hrec]
      rfl
  have hgenName : E.lowered.recursors.canonicalGeneration.recursorName owner =
      E.lowered.recursors.generationSignature.families[owner].name.str "rec" :=
    E.lowered.recursorConstruction.generator.names owner
  rw [hgenName] at hename
  obtain ⟨c, hcdef⟩ : ∃ c, c =
      E.lowered.recursors.generationSignature.families[owner].name.str "rec" :=
    ⟨_, rfl⟩
  rw [← hcdef] at hename
  rcases r'.recursorName_cases c with hsame | ⟨p, hp, hpc, hpname⟩
  · rw [hsame] at hename
    have hnc : n = c := hname.symm.trans hename
    -- `c` is the lowered recursor name of a lowered family
    obtain ⟨src, hsrc, hsrcName, -⟩ :=
      E.lowered.recursorConstruction.generator.models.family owner
    have hcRec : c ∈ E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") :=
      List.mem_map.mpr ⟨src, hsrc, by
        rw [hcdef]; exact (congrArg (fun n : Name => n.str "rec") hsrcName).symm⟩
    simp only [Restoration.restorableNames, List.mem_append] at hn'
    rcases hn' with hhead | hfst
    · rw [compilationRestoration_heads_auxiliary, hheadNames] at hhead
      have hfam : n ∈ familyNames E.lowered.loweredDecl.types := by
        obtain ⟨t, ht, h⟩ := mem_familyNames.mp hhead
        exact mem_familyNames.mpr ⟨t, List.mem_of_mem_drop ht, h⟩
      exact (List.nodup_append.mp hnodup).2.2 _ hfam _ (hnc ▸ hcRec) rfl
    · exact hnot c (hnc ▸ hfst) (hsame.trans hnc.symm)
  · exact hnot c (List.mem_map.mpr ⟨p, hp, hpc⟩) (hename.symm.trans hname)

/-! ### Commutation under input-side trailing avoidance -/

section Commutation


/-- Syntax translated in an environment lacking the restorable names outside
`X`, and avoiding `X` itself, avoids every restorable name. -/
theorem avoidsRestorable_of_partial {r : Restoration} {X : List Name}
    {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (Hfresh : ∀ n ∈ r.restorableNames, n ∉ X → env.constants n = none)
    (H : TrExprS env Us Δ e e') (hX : e.AvoidsConsts X) :
    e.AvoidsConsts r.restorableNames := by
  classical
  have h₁ : e.AvoidsConsts (r.restorableNames.filter (fun n => n ∉ X)) :=
    checkPositivityStep.TrExprS.sourceAvoidsFresh (fun n hn => by
      simp only [List.mem_filter, decide_eq_true_eq] at hn
      exact Hfresh n hn.1 hn.2) H
  refine Lean.Expr.AvoidsConsts.of_cover (fun n hn => ?_) h₁ hX
  by_cases hnX : n ∈ X
  · exact .inr hnX
  · exact .inl (by simp [hn, hnX])

/-- The head-occurrence case of `restorationCommutesTrail`. -/
theorem restorationCommutesTrail_paramUniform
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    {X : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, n ∉ X → targetEnv.constants n = none)
    {e : Expr} {c : Name} {us : List Level} {Δs Δt : VLCtx} {s t : VExpr}
    (hfn : e.getAppFn = .const c us) (hmem : c ∈ r.heads.map (·.auxiliary))
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Htrail : e.TrailingArgsAvoid (r.heads.map (·.auxiliary)) X result.nparams)
    (Hctx : RestoreCtxRel r Δs Δt)
    (Hs : TrExprS sourceEnv Us Δs e s)
    (Ht : TrExprS targetEnv Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t) :
    r.expr s = some t := by
  obtain ⟨hus, rest, hargs, -⟩ := Hshape.getAppFn_const_head_inv hfn hmem
  subst us
  have hAsLen : As.toList.length = result.nparams := by simpa using hsize
  have hrestX : ∀ a ∈ rest, a.AvoidsConsts X := by
    intro a ha
    apply Htrail.trail hfn hmem
    rw [hargs, ← hAsLen, List.drop_left]
    exact ha
  have hhead : restoreHead result env As c ≠ none :=
    (A.restoreHead_ne_none_iff As c).mpr hmem
  rcases Option.ne_none_iff_exists.mp hhead with ⟨H, hH⟩
  have hH := hH.symm
  have hnotrec := A.notRecursor_of_head hhead
  have hnode := restoreNestedNode_eq_of_restoreHead result env As auxRec e
    (fun c' ls' heq => by subst heq; cases hfn; exact hnotrec) hfn hH
    (by rw [hargs]; simp [hAsLen])
  rw [Expr.replace_of_some hnode, hargs, ← hAsLen, List.drop_left] at Ht
  have he : e = Expr.mkAppList (.const c auxLevels) (As.toList ++ rest) := by
    rw [← hargs, ← hfn, Expr.mkAppList_getAppArgsList]
  subst he
  rcases checkPositivityStep.TrExprS.mkAppList_inv Hs with ⟨fn', L', hfn', hL', rfl⟩
  cases hfn' with
  | const _ hlsV _ =>
  obtain ⟨P', R'', rfl, hP', hR''⟩ := List.Forall₂.append_inv hL'
  rcases checkPositivityStep.TrExprS.mkAppList_inv Ht with ⟨Hv, R', hHv, hR', rfl⟩
  rcases A.head As c H hH with ⟨h, hfind, hnparams, hlevels⟩
  rcases hlevels _ hlsV with ⟨huvars, hsem⟩
  obtain ⟨PT, hPT, hPr⟩ := Hctx.translate_fvars hc HAs hP'
  have hHvEq := hsem Δt PT Hv HAs hsize hPT hHv
  subst hHvEq
  have hrest : ∀ a ∈ rest, a.AvoidsConsts r.restorableNames := by
    intro a ha
    obtain ⟨b, -, hab⟩ := Lean4Lean.List.Forall₂.forall_exists_l hR' a ha
    exact avoidsRestorable_of_partial Hfresh hab (hrestX a ha)
  have hRr := Hctx.translate_avoids_forall₂ hc hrest hR'' hR'
  have hPTlen : PT.length = result.nparams := by
    rw [← Lean4Lean.List.Forall₂.length_eq hPT, hAsLen]
  simp only [Restoration.expr]
  rw [Restoration.expr.go_mkApps r (List.Forall₂.append' hPr hRr), List.append_nil]
  have hle : h.nparams ≤ (PT ++ R').length := by simp [hnparams, hPTlen]
  simp [Restoration.expr.go, hfind, HeadSpecialization.apply, huvars, hnparams, hPTlen,
    Lean4Lean.VExpr.mkApps_append]

/-- **Commutation of executable restoration with `Restoration.expr`, with
input-side avoidance.** As `restorationCommutes`, but the restorable names
need only be fresh in `targetEnv` outside a list `X`; the names of `X` are
instead required to be avoided by the trailing arguments of the head
occurrences and by the literals of the input (`Expr.TrailingArgsAvoid`). With
`X = []` this is `restorationCommutes`; with `X = r.restorableNames` no environment freshness
is needed at all. -/
theorem restorationCommutesTrail
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    {X : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, n ∉ X → targetEnv.constants n = none)
    {e : Expr} {Δs Δt : VLCtx} {s t : VExpr}
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Htrail : e.TrailingArgsAvoid (r.heads.map (·.auxiliary)) X result.nparams)
    (Hctx : RestoreCtxRel r Δs Δt)
    (Hs : TrExprS sourceEnv Us Δs e s)
    (Ht : TrExprS targetEnv Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t) :
    r.expr s = some t := by
  have hmiss : ∀ x : Expr, (∀ c us, x ≠ .const c us) → (∀ c us, x.getAppFn ≠ .const c us) →
      result.restoreNestedNode env As auxRec x = none := fun x h1 h2 =>
    restoreNestedNode_eq_none_of_restoreHead result env As auxRec x
      (fun c us h => absurd h (h1 c us)) (fun c us h => absurd h (h2 c us))
  induction Hs generalizing Δt t with
  | bvar h =>
    rw [Expr.replace_bvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | bvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | fvar h =>
    rw [Expr.replace_fvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | fvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | sort h =>
    rw [Expr.replace_sort_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | sort h' => cases h.symm.trans h'; rfl
  | @const c _ _ _ us hcs hls hlen =>
    by_cases hmem : c ∈ r.heads.map (·.auxiliary)
    · exact restorationCommutesTrail_paramUniform A hc HAs hsize Hfresh rfl hmem Hshape Htrail Hctx
        (.const hcs hls hlen) Ht
    · have hnone := A.restoreHead_eq_none (As := As) hmem
      cases hrec : auxRec.find? c with
      | some new =>
        rw [Expr.replace_of_some (restoreNestedNode_recursor result env As auxRec c new us
          hrec)] at Ht
        cases Ht with
        | const _ hls' _ =>
          cases hls.symm.trans hls'
          simp only [Restoration.expr]
          rw [A.go_const (As := As) hnone]
          simp [hrec, VExpr.mkApps]
      | none =>
        rw [Expr.replace_const_of_none (restoreNestedNode_eq_none_of_restoreHead result env
          As auxRec _ (fun c' ls' heq => by cases heq; exact hrec)
          (fun c' ls' h => by
            simp only [Expr.getAppFn, Expr.const.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hnone))] at Ht
        cases Ht with
        | const _ hls' _ =>
          cases hls.symm.trans hls'
          simp only [Restoration.expr]
          rw [A.go_const (As := As) hnone]
          simp [hrec, VExpr.mkApps]
  | @app _ _ _ _ _ f a h1 h2 hf ha ihf iha =>
    by_cases hhit : ∃ c us, (Expr.app f a).getAppFn = .const c us ∧
        c ∈ r.heads.map (·.auxiliary)
    · obtain ⟨c, us, hfn, hmem⟩ := hhit
      exact restorationCommutesTrail_paramUniform A hc HAs hsize Hfresh hfn hmem Hshape Htrail Hctx
        (.app h1 h2 hf ha) Ht
    · have hnot : ∀ c us, f.getAppFn = .const c us → c ∉ r.heads.map (·.auxiliary) :=
        fun c us hfn hmem => hhit ⟨c, us, by simpa [Expr.getAppFn] using hfn, hmem⟩
      obtain ⟨Hf, Ha⟩ := Hshape.app_inv hnot
      cases Htrail with
      | app Tf Ta _ =>
      have hnone : result.restoreNestedNode env As auxRec (.app f a) = none :=
        restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
          (by intro _ _ h; cases h)
          (fun c us hfn => A.restoreHead_eq_none
            (hnot c us (by simpa [Expr.getAppFn] using hfn)))
      rw [Expr.replace_app_of_none hnone] at Ht
      cases Ht with
      | app _ _ htf hta =>
        exact restoration_expr_app (ihf Hf Tf Hctx htf) (iha Ha Ta Hctx hta)
  | lam _ _ _ ihd ihb =>
    obtain ⟨Hd, Hb⟩ := Hshape.lam_inv
    cases Htrail with
    | lam Td Tb =>
    rw [Expr.replace_lam_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | lam _ htd htb =>
      exact restoration_expr_lam (ihd Hd Td Hctx htd) (ihb Hb Tb Hctx.vlam htb)
  | forallE _ _ _ _ ihd ihb =>
    obtain ⟨Hd, Hb⟩ := Hshape.forallE_inv
    cases Htrail with
    | forallE Td Tb =>
    rw [Expr.replace_forallE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | forallE _ _ htd htb =>
      exact restoration_expr_forallE (ihd Hd Td Hctx htd) (ihb Hb Tb Hctx.vlam htb)
  | letE _ _ _ _ _ ihv ihb =>
    obtain ⟨-, Hv, Hb⟩ := Hshape.letE_inv
    cases Htrail with
    | letE _ Tv Tb =>
    rw [Expr.replace_letE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | letE _ _ htv htb => exact ihb Hb Tb (Hctx.vlet (ihv Hv Tv Hctx htv)) htb
  | lit _ hs _ =>
    rw [Expr.replace_lit_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Htrail with
    | lit _ hX =>
    have Havoid := avoidsRestorable_of_partial Hfresh Ht hX
    cases Ht with
    | lit _ ht =>
      cases Havoid with
      | lit _ Ha => exact Hctx.translate_avoids hc Ha hs ht
  | mdata _ ih =>
    have He := Hshape.mdata_inv
    cases Htrail with
    | mdata Te =>
    rw [Expr.replace_mdata_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | mdata ht => exact ih He Te Hctx ht
  | proj _ hp ih =>
    have He := Hshape.proj_inv
    cases Htrail with
    | proj Te =>
    rw [Expr.replace_proj_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | proj ht hp' =>
      exact restoration_expr_proj (ih He Te Hctx ht)

/-- The unchanged parameter prefix of a lambda restoration, with input-side
avoidance of `X` for the shared domains. -/
theorem Expr.SameLambdaPrefix.translatedDomains_restoreTrail {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name} {X : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, n ∉ X → envT.constants n = none)
    {n : Nat} {left right : Expr} (Hsame : Expr.SameLambdaPrefix n left right)
    (Hdom : left.LamPrefixAvoids X n) :
    ∀ {Δ₁ Δ₂ : VLCtx} {D₁ D₂ : List VExpr} {X₁ X₂ : VExpr},
      RestoreCtxRel r Δ₁ Δ₂ →
      TrExprS envS Us Δ₁ left (VExpr.wrapLams D₁ X₁) →
      TrExprS envT Us Δ₂ right (VExpr.wrapLams D₂ X₂) →
      D₁.length = n → D₂.length = n →
      List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ := by
  induction Hsame with
  | nil =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ _ _ _ h₁ h₂
    rw [List.eq_nil_of_length_eq_zero h₁, List.eq_nil_of_length_eq_zero h₂]
    exact .nil
  | cons _ ih =>
    cases Hdom with
    | succ hdX Hrest =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ Hctx H₁ H₂ h₁ h₂
    cases D₁ with
    | nil => simp at h₁
    | cons d₁ D₁ =>
    cases D₂ with
    | nil => simp at h₂
    | cons d₂ D₂ =>
    simp only [VExpr.wrapLams, List.foldr_cons] at H₁ H₂
    cases H₁ with
    | lam _ hd₁ hb₁ =>
    cases H₂ with
    | lam _ hd₂ hb₂ =>
    exact .cons
      (Hctx.translate_avoids hc (avoidsRestorable_of_partial Hfresh hd₂ hdX) hd₁ hd₂)
      (ih Hrest Hctx.vlam hb₁ hb₂ (by simpa using h₁) (by simpa using h₂))

/-- **Closed-term commutation for lambda telescopes with input-side
avoidance**: the lambda-telescope analogue of
`NestedRestorationOpening.restorationCommutes`, with the freshness of the names
of `X` replaced by their avoidance in the input. -/
theorem NestedRestorationOpening.restorationCommutesLamTrail
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {X : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, n ∉ X → targetEnv.constants n = none)
    (Hshape : Hopen.body.ParamUniform (r.heads.map (·.auxiliary)) Hopen.params.toList auxLevels)
    (Htrail : input.TrailingArgsAvoid (r.heads.map (·.auxiliary)) X result.nparams)
    (Hdom : input.LamPrefixAvoids X result.nparams)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (hnotForall : input.isForall = false)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (hrestored : Closed Hopen.restoredBody)
    (Hs : TrExprS sourceEnv Us [] input s) (Ht : TrExprS targetEnv Us [] output t) :
    r.expr s = some t := by
  have hnodup := Hopen.selectionNodup
  have hlen : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selection.size.symm.trans Hopen.opening.initial_size
  have hparams := Hopen.selection.expressions
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [hparams]; simpa using hlen
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars', hAs, _, hbody⟩
  have hfvars : fvars'.map Expr.fvar = Hopen.selection.fvars.map Expr.fvar := by
    have h1 : Hopen.params.toList = Hopen.selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList hparams
    rw [h1] at hAs
    simpa using hAs.symm
  rw [hfvars] at hbody
  have HbodyTrail : Hopen.body.TrailingArgsAvoid (r.heads.map (·.auxiliary)) X
      result.nparams := by
    rw [hbody]
    exact (Htrail.lambdaTelescope Htel).instantiateRevList_fvars _ 0
  rcases TrExprS.lambdaTelescope_shape_with_context Htel Hs with
    ⟨Ds, sR, hDs, rfl, HsR⟩
  have HbodyS := TrExprS.instantiateRevFVars Hopen.selection.fvars Ds [] suffix sR
    (hlen.trans hDs.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HsR _) HsR
  rw [← hbody, List.append_nil] at HbodyS
  have houtput : output = Hopen.lctx.mkLambda Hopen.params Hopen.restoredBody := by
    simpa [hnotForall] using Hopen.output_eq
  have HoutTel : Expr.LambdaTelescope output Hopen.selection.fvars.length
      (Hopen.restoredBody.abstractList Hopen.selection.fvars) := by
    have Htelescope := LocalContext.mkLambda_fvars_lambdaTelescopeList
      (body := Hopen.restoredBody) Hopen.selection.declarations hnodup hrestored
    simpa only [← Hopen.selection.expressions, ← houtput] using Htelescope
  rcases TrExprS.lambdaTelescope_shape_with_context HoutTel Ht with ⟨Dt, tR, hDt, rfl, HtR⟩
  have HbodyT := TrExprS.instantiateRevFVars Hopen.selection.fvars Dt [] _ tR
    hDt.symm hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HtR _) HtR
  rw [TypeChecker.Expr.abstractList_instantiateRevList_eq_self hnodup hrestored,
    List.append_nil, Hopen.replacement.eq_replace] at HbodyT
  have Hbody := restorationCommutesTrail A hc HAs hsize Hfresh Hshape HbodyTrail
    (fvarScope_vlamShape _ Ds Dt (hDs.trans (hlen.symm.trans hDt.symm))).restoreCtxRel
    HbodyS HbodyT
  have hinput : Hopen.lctx.mkLambda Hopen.params Hopen.body = input :=
    Hopen.opening.root_mkLambda_tail Hopen.lctxWF Htel (FVarsIn_to_FVarIdsIn Hinput) hclosed
  have Hsame : Expr.SameLambdaPrefix Hopen.params.size input output := by
    have := Hopen.selection.sameLambdaPrefix hnodup Hopen.body Hopen.restoredBody
    rwa [hinput, ← houtput] at this
  rw [hsize] at Hsame
  exact restoration_expr_wrapLams
    (Hsame.translatedDomains_restoreTrail hc Hfresh Hdom .nil Hs Ht hDs (hDt.trans hlen))
    Hbody

/-- **The restored right-hand side of one rule, with input-side avoidance.**
The restored right-hand side translates the restoration of the generated
equation, provided the restorable names are fresh in `trEnv` outside a list
`X` and the lowered rule right-hand sides of the step avoid `X` in the trailing
arguments of their head occurrences, in their literals and in their parameter
domains (`Htrail`). For `X` the renamed recursor names, the freshness holds in
the recursor environment of every restored block without hypotheses
(`recursorVEnv_restorableNames_fresh_of_not_renamed`); for
`X = restorableNames` no freshness is needed. -/
theorem NestedRun.restoredRuleRhs_of_trail
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {trEnv : VEnv} {X : List Name}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → trEnv.constants n = none)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.lowered.recursors.canonicalGeneration.recursorName owner) s t)
    (Htrail : ∀ rule ∈ Hstep.oldInfo.rules,
      rule.rhs.TrailingArgsAvoid
          ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary)) X
          result.nparams ∧
        rule.rhs.LamPrefixAvoids X result.nparams)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    (hk : k.val = recursorMinorOffset E.lowered.indTypes owner.val + j)
    {rhs : VExpr}
    (Ht : TrExprS trEnv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rhs) :
    (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.recursors.canonicalGeneration.equation k).rhs = some rhs := by
  let P := E.lowered.recursors
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hlenRules := Hstep.restored.restoration.rules.length
  have hjOld : j < Hstep.oldInfo.rules.length := hlenRules ▸ hj
  have hjGen : j < (P.generated.entry owner.val hi).info.rules.length := by
    rw [hinfo]; exact hjOld
  have hkb : recursorMinorOffset E.lowered.indTypes owner.val + j <
      P.generationSignature.constructors.size := hk ▸ k.isLt
  have Hs0 := P.ruleRhsTranslations owner.val hi j hjGen hkb
  have hkfin : (⟨recursorMinorOffset E.lowered.indTypes owner.val + j, hkb⟩ :
      Fin P.generationSignature.constructors.size) = k := Fin.ext hk.symm
  rw [hkfin] at Hs0
  have hlevels : (P.generated.entry owner.val hi).info.levelParams =
      AddInductive.getRecLevelParams P.elimLevel E.lowered.c.lparams := by
    rw [(P.generated.entry owner.val hi).levels, P.localExtends.lparams_eq]
  rw [← hlevels] at Hs0
  have Hs : TrExprS P.outVEnv Hstep.oldInfo.levelParams []
      (Hstep.oldInfo.rules[j]'hjOld).rhs (P.canonicalGeneration.equation k).rhs := by
    have key : ∀ (info : RecursorVal) (h : j < info.rules.length),
        info = Hstep.oldInfo →
        TrExprS P.outVEnv info.levelParams [] (info.rules[j]'h).rhs
          (P.canonicalGeneration.equation k).rhs →
        TrExprS P.outVEnv Hstep.oldInfo.levelParams []
          (Hstep.oldInfo.rules[j]'hjOld).rhs (P.canonicalGeneration.equation k).rhs := by
      intro info h hinfo' H
      subst hinfo'
      exact H
    exact key _ hjGen hinfo Hs0
  -- the rule restoration
  have Hrule := Hstep.restored.restoration.rules.entry j hjOld hj
  rcases Hrule.rhs.opening hparamsSize with ⟨Hopen⟩
  -- the telescope
  have Hshape := (E.recursorParamUniform_of_wfCore wf Hsources owner Hstep).2 _ (List.getElem_mem hjOld)
  rw [← hheads] at Hshape
  have hnp : result.nparams = P.generationSignature.params.length := by
    rw [← E.statsParamsSize]; exact P.params_size_eq
  have hfam : 0 < P.generationSignature.families.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) owner.isLt
  obtain ⟨d, Ds, X, hrhsEq, hlenD⟩ : ∃ d Ds X,
      (P.canonicalGeneration.equation k).rhs = VExpr.wrapLams (d :: Ds) X ∧
        result.nparams ≤ (d :: Ds).length := by
    have hlen : P.generationSignature.params.length + 1 ≤
        (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)).length := by
      simp only [List.length_append, Instance.params, Instance.motives, List.length_map,
        List.length_zipIdx, Array.length_toList]
      omega
    obtain ⟨X, hX⟩ : ∃ X, (P.canonicalGeneration.equation k).rhs =
        VExpr.wrapLams (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)) X := ⟨_, rfl⟩
    revert hlen hX
    generalize (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)) = L
    intro hlen hX
    cases L with
    | nil => simp at hlen
    | cons d Ds => exact ⟨d, Ds, X, hX, by simp only [List.length_cons] at hlen ⊢; omega⟩
  rw [hrhsEq] at Hs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  have Htel := Hlead.lambdaTelescope_of_tr Hs hlenD
  have hclosed : Closed (Hstep.oldInfo.rules[j]'hjOld).rhs := by
    simpa [VLCtx.bvars] using Hs.closed
  have Hinput : (Hstep.oldInfo.rules[j]'hjOld).rhs.FVarsIn fun _ => False :=
    Hs.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h
  have HbodyShape := Hopen.paramUniform_of_lowered_lam Htel ⟨body, Hlead, HB⟩
  have hrestored := Hopen.restoredBody_closed_lam D Htel
    (by simpa using Htel.closed_result hclosed)
  have Ht' : TrExprS trEnv Hstep.oldInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rhs := by
    rw [← Hstep.restored.restoration.levelParams]; exact Ht
  rw [hrhsEq]
  have HtrailJ := Htrail _ (List.getElem_mem hjOld)
  exact Hopen.restorationCommutesLamTrail (D.agreement trEnv _) hscoped.argumentsClosed Hfresh
    HbodyShape HtrailJ.1 HtrailJ.2 Htel (TrExprS.isForall_false_of_wrapLams Hs) Hinput hclosed
    hrestored Hs Ht'

end Commutation

/-! ### Restored equations modulo a list of names -/

/-- **Input-side avoidance of the lowered recursor rules** (a property of the
lowered environment): every rule right-hand side of the lowered recursor of
every generated owner avoids `X` in the trailing arguments of its head occurrences
(`Expr.TrailingArgsAvoid heads X`), in its literals, and in its first
`result.nparams` lambda domains. -/
def NestedRun.LoweredRulesAvoid
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (heads X : List Name) : Prop :=
  ∀ (owner : Fin E.lowered.recursors.generationSignature.families.size)
    (rec : RecursorVal),
    E.loweredEnv.find?
        (E.lowered.recursors.canonicalGeneration.recursorName owner) =
      some (.recInfo rec) →
    ∀ rule ∈ rec.rules,
      rule.rhs.TrailingArgsAvoid heads X result.nparams ∧
        rule.rhs.LamPrefixAvoids X result.nparams

/-- **Translation of a restored equation list modulo `X`**: the executable
restored rules translate, rule by rule (`TrRestoredRecursorRule`), to `rules` in
an environment that lacks the restorable names outside `X`. -/
def NestedRun.TrRestoredRulesModulo
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (r : Restoration) (X : List Name) (rules : List VDefEq) : Prop :=
  ∃ trEnv : VEnv, (∀ n ∈ r.restorableNames, n ∉ X → trEnv.constants n = none) ∧
    List.Forall₂ (E.TrRestoredRecursorRule r trEnv)
      (List.finRange
        E.lowered.recursors.generationSignature.constructors.size)
      rules

/-- Freshness outside `X` is freshness outside the restorable names of `X`. -/
theorem fresh_filter_restorable {R X : List Name} {P : Name → Prop}
    (H : ∀ n ∈ R, n ∉ X → P n) : ∀ n ∈ R, n ∉ X.filter (· ∈ R) → P n := by
  intro n hn hnX
  refine H n hn fun hX => hnX ?_
  simp [List.mem_filter, hX, hn]

/-- Translation modulo `X` is translation modulo the restorable names of `X`. -/
theorem NestedRun.TrRestoredRulesModulo.filter_restorable
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv}
    {r : Restoration} {X : List Name} {rules : List VDefEq}
    (H : E.TrRestoredRulesModulo r X rules) :
    E.TrRestoredRulesModulo r (X.filter (· ∈ r.restorableNames)) rules := by
  obtain ⟨trEnv, Hfresh, HF⟩ := H
  exact ⟨trEnv, fresh_filter_restorable Hfresh, HF⟩

/-- **One restored equation, modulo `X`.** -/
theorem NestedRun.restoredEquation_of_trModulo
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {X : List Name}
    (HL : E.LoweredRulesAvoid
      ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary)) X)
    {trEnv : VEnv}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → trEnv.constants n = none)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    {rule : VDefEq}
    (H : E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries) trEnv k
      rule) :
    (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule := by
  obtain ⟨owner, j, s, t, Hstep, hj, hk, huvars, Ht, hlhs, htype⟩ := H
  have hrhs := E.restoredRuleRhs_of_trail wf Hsources hheads hparamsSize D hscoped Hfresh owner
    Hstep (HL owner Hstep.oldInfo Hstep.lookup) j hj k hk Ht
  simp only [Restoration.equation, hlhs, hrhs, htype, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq]
  cases rule
  simp only at huvars
  rw [huvars]

/-- **The restored equation list, modulo `X`.** If an abstract equation list
translates the executable restored rules in an environment lacking the
restorable names outside `X`, and the lowered rules avoid `X` at their head occurrences,
it is the restored generated equation list. -/
theorem NestedRun.restoredEquations_of_trModulo
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {X : List Name}
    (HL : E.LoweredRulesAvoid
      ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary)) X)
    {rules : List VDefEq}
    (H : E.TrRestoredRulesModulo (compilationRestoration sourceDecl auxiliaries) X
      rules) :
    E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some rules := by
  obtain ⟨trEnv, Hfresh, HF⟩ := H
  show List.mapM _ ((List.finRange _).map _) = _
  rw [List.mapM_map]
  exact List.mapM_eq_some.mpr (Lean4Lean.List.Forall₂.imp (fun k _ h =>
    E.restoredEquation_of_trModulo wf Hsources hheads hparamsSize D hscoped HL
      Hfresh k h) HF)


/-! ### Shape of the renamed recursor names -/

theorem _root_.Lean.Name.appendIndexAfter_str_rec (M : Name) (k : Nat) :
    ∃ s, (M.str "rec").appendIndexAfter k = .str M s := by
  have h : (M.str "rec").hasMacroScopes = false := by
    simp [Name.hasMacroScopes]
  simp only [Name.appendIndexAfter, Name.modifyBase, h, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

/-- Every renamed recursor name of a compilation restoration is a string
extension `M.s` of the first source family name `M`. -/
theorem _root_.Lean4Lean.InductiveSignature.compilationRestoration_recursors_snd_str
    (source : VInductDecl) (auxiliaries : List ContainerSpecialization) :
    ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      ∃ s, p.2 = .str (((source.types.head?).map (fun t : VInductiveType => t.name)).getD
        (default : Name)) s := by
  intro p hp
  simp only [compilationRestoration, List.mem_map] at hp
  obtain ⟨⟨a, i⟩, -, rfl⟩ := hp
  exact Name.appendIndexAfter_str_rec _ _

/-- **Lowered auxiliary recursor names are never renamed recursor names.** The
renamed names `M.s` extend the first source family name `M`, while a lowered
auxiliary recursor name is `A.rec` for an auxiliary family `A`, which is
distinct from `M` (lowered family names are distinct, and `A` lies in the
reserved `_nested` namespace). -/
theorem NestedRun.auxRecName_not_renamed
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∉
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd := by
  intro a ha hmem
  obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hmem
  obtain ⟨s, hs⟩ := compilationRestoration_recursors_snd_str sourceDecl auxiliaries p hp
  have hMA : ((sourceDecl.types.head?).map (fun t : VInductiveType => t.name)).getD
      (default : Name) = a.auxiliary := (Name.str.inj (hs.symm.trans hpa)).1
  obtain ⟨-, -, -, -, -, hreserved, hkeys, hnodup⟩ := E.auxHeadsFacts wf Hsources
  obtain ⟨nested, hnested⟩ := D.familyLookup a ha
  have hA : a.auxiliary ∈ E.auxHeads := hkeys _ _ hnested
  cases htypes : sourceDecl.types with
  | nil =>
    rw [htypes] at hMA
    have h := hreserved _ hA
    rw [← hMA] at h
    simp [default, Name.isPrefixOf] at h
  | cons t ts =>
    rw [htypes] at hMA
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at hMA
    -- the first source family is the first lowered family
    have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
      have Hcore := E.sourceCore.core
      rw [E.sourceCoreDecl_eq] at Hcore
      exact (forall₂_trInductiveType_names Hcore.types).symm
    have hlen : sourceTypes.length = sourceDecl.types.length := by
      simpa using congrArg List.length hnames
    have hsrc := E.sourceNames_eq
    rw [hnames, hlen] at hsrc
    have htake : t.name ∈ familyNames
        (E.lowered.loweredDecl.types.take sourceDecl.types.length) := by
      have : t.name ∈ sourceDecl.types.map (·.name) := by simp [htypes]
      rw [hsrc] at this
      obtain ⟨t', ht', heq⟩ := List.mem_map.mp this
      rw [← heq]
      exact mem_familyNames_of_type ht'
    have hdrop : a.auxiliary ∈ familyNames
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := hA
    have hfam := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types,
      familyNames, List.flatMap_append] at hfam
    exact (List.nodup_append.mp hfam).2.2 _ htake _ hdrop hMA

/-! ### The rule premise modulo the renamed recursor names -/

/-- **The rule premise of the nested installation without any naming hypothesis**:
a `RestoredBlockDerivation` whose rules translate the executable restored rules,
with freshness of the restorable names in its recursor environment weakened to
the restorable names that are not renamed recursor names
(`recursorVEnv_restorableNames_fresh_of_not_renamed`). This is the strongest
freshness conclusion available: a renamed recursor name that coincides with a
restorable name is installed in every such recursor environment. -/
theorem NestedRun.hrules_of_modulo
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HruleShape : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules)) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.recursorVEnv.constants n = none) ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules) := by
  intro auxiliaries D
  obtain ⟨C, hC, HC⟩ := HruleShape auxiliaries D
  exact ⟨C, hC, E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC D, HC⟩

end VerifyInductive
end Lean4Lean
