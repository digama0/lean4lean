import Lean4Lean.Theory.Typing.Interpretation
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Theory.Inductive.RestorationProjNames
import Lean4Lean.Theory.Inductive.ProjNamesAvoid
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Typing.EliminatorRestorationScope
import Lean4Lean.Theory.Inductive.CaseTypeClosed

/-! # Restoration as an environment interpretation

The partial syntactic operation `Restoration.expr` (`Theory/Inductive/Restoration.lean`)
substitutes the actual parameters into each fully applied auxiliary head and renames the
auxiliary recursors. Its metatheory goes through the environment interpretation
(`Theory/Typing/Interpretation.lean`) that interprets each auxiliary head by the closed lambda
telescope `λ params, target levels arguments` over the common parameters
(`Restoration.lambdaReplacement`) and renames every other constant by the recursor renaming
(`Restoration.renaming`), the *restoration interpretation* `Restoration.interpretation`.

* `Restoration.Agrees r I`: the interpretation `I` interprets every head of `r` by the parameter
  abstraction of its specialization and otherwise renames by the recursor renaming. Then the
  restoration of a term whose projection owners `I` fixes is a beta reduct of its interpretation
  (`Restoration.Agrees.expr_betaRed`), hence definitionally equal to it at every type in a
  well-formed context of an environment with beta subject reduction
  (`Restoration.Agrees.expr_simAt`).
* `Restoration.Substitution envS envL r I`: a sound interpretation of `envL` in `envS` for
  well-formed contexts that agrees with `r`. It transports closed typing judgments and
  equations of `envL` to their restorations in `envS` (`Restoration.expr_hasType`,
  `Restoration.equation_wf`, `Restoration.expr_isDefEqU`).
* `VEnv.RestoredEliminator`: a restoration-free eliminator of `envL` matched in `envS` by the
  registered schema with the same signature and an agreeing restoration. Its rules hold after
  interpretation in well-formed contexts, by the agreement up to beta
  (`RestoredEliminator.clause`, an `EliminatorClause` for `VEnv.TypedCtx`); this is the one
  eliminator clause that needs a context invariant.
-/

namespace Lean4Lean

open VEnv

namespace InductiveSignature

/-! ### The restoration interpretation -/

/-- The lambda replacement of a restoration table, given a parameter
telescope (outermost first) for each head. -/
def Restoration.lambdaReplacement (r : Restoration)
    (domains : HeadSpecialization → List VExpr) : Name → Option VExpr := fun c =>
  (r.heads.find? (fun h => h.auxiliary == c)).map fun h =>
    VExpr.wrapLams (domains h) (VExpr.mkApps (.const h.target h.levels) h.arguments)

/-- The renaming of a restoration: heads are renamed to their targets (this
only matters for projection owners), every other name by the recursor
renaming. -/
def Restoration.renaming (r : Restoration) (n : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == n) with
  | some h => h.target
  | none => r.recursorName n

/-- **The restoration interpretation** over the common parameter telescope `P`: each head is
interpreted by its lambda replacement, every other constant and every projection owner is
renamed by the restoration renaming. -/
def Restoration.interpretation (r : Restoration) (P : List VExpr) : Interpretation where
  consts := r.lambdaReplacement fun _ => P
  rename := r.renaming

/-- The restoration interpretation keeping every projection owner. -/
abbrev Restoration.constInterpretation (r : Restoration) (P : List VExpr) : Interpretation :=
  { r.interpretation P with projOwner := id }

@[simp] theorem Restoration.interpretation_consts (r : Restoration) (P : List VExpr) :
    (r.interpretation P).consts = r.lambdaReplacement fun _ => P := rfl

@[simp] theorem Restoration.interpretation_rename (r : Restoration) (P : List VExpr) :
    (r.interpretation P).rename = r.renaming := rfl

@[simp] theorem Restoration.interpretation_projOwner (r : Restoration) (P : List VExpr) :
    (r.interpretation P).projOwner = r.renaming := rfl

@[simp] theorem Restoration.interpretation_elim (r : Restoration) (P : List VExpr) :
    (r.interpretation P).elim = fun block owner => (block, owner) := rfl

theorem Restoration.lambdaReplacement_shape (r : Restoration)
    {domains : HeadSpecialization → List VExpr}
    (hdomains : ∀ h ∈ r.heads, (domains h).length = h.nparams)
    (hρ : r.lambdaReplacement domains c = some t) : ∃ h doms,
      r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
      t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments) := by
  unfold Restoration.lambdaReplacement at hρ
  cases hfind : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hfind] at hρ
  | some h =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hρ
    exact ⟨h, domains h, rfl, hdomains h (List.mem_of_find?_eq_some hfind), hρ.symm⟩

theorem Restoration.lambdaReplacement_ne_forallE (r : Restoration)
    {domains : HeadSpecialization → List VExpr}
    (hρ : r.lambdaReplacement domains c = some t) : ∀ A B, t ≠ .forallE A B := by
  unfold Restoration.lambdaReplacement at hρ
  cases hfind : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hfind] at hρ
  | some h =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hρ
    subst hρ
    intro A B
    cases hd : domains h with
    | nil =>
      simp only [VExpr.wrapLams, List.foldr]
      exact VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) _
    | cons d ds => intro h; simp [VExpr.wrapLams] at h

theorem Restoration.lambdaReplacement_eq_none {r : Restoration}
    {domains : HeadSpecialization → List VExpr} {c : Name}
    (h : c ∉ r.heads.map (·.auxiliary)) : r.lambdaReplacement domains c = none := by
  simp [Restoration.lambdaReplacement, Restoration.heads_find?_eq_none h]

theorem Restoration.lambdaReplacement_eq_none_of_not_restorable {r : Restoration}
    {domains : HeadSpecialization → List VExpr} {n : Name}
    (h : n ∉ r.restorableNames) : r.lambdaReplacement domains n = none :=
  Restoration.lambdaReplacement_eq_none fun hm => h (List.mem_append_left _ hm)

theorem Restoration.renaming_of_find_none {r : Restoration} {n : Name}
    (h : r.heads.find? (fun h => h.auxiliary == n) = none) :
    r.renaming n = r.recursorName n := by
  simp [Restoration.renaming, h]

theorem Restoration.renaming_eq_self {r : Restoration} {n : Name}
    (h : n ∉ r.restorableNames) : r.renaming n = n := by
  have h1 : n ∉ r.heads.map (·.auxiliary) := fun hm => h (List.mem_append_left _ hm)
  have h2 : n ∉ r.recursors.map Prod.fst := fun hm => h (List.mem_append_right _ hm)
  rw [Restoration.renaming_of_find_none (Restoration.heads_find?_eq_none h1),
    Restoration.recursorName_of_not_mem h2]

/-- The lambda replacement over a closed telescope is closed. -/
theorem Restoration.interpretation_closed {r : Restoration} {P : List VExpr}
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length)
    (hargs : ∀ h ∈ r.heads, ∀ arg ∈ h.arguments, arg.ClosedN h.nparams)
    (hPclosed : ∀ i (hi : i < P.length), P[i].ClosedN i) :
    (r.interpretation P).Closed := by
  intro c t hρ
  change r.lambdaReplacement (fun _ => P) c = some t at hρ
  unfold Restoration.lambdaReplacement at hρ
  cases hf : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hf] at hρ
  | some h =>
    simp only [hf, Option.map_some, Option.some.injEq] at hρ
    subst hρ
    have hmem := List.mem_of_find?_eq_some hf
    refine VExpr.ClosedN.wrapLams_closed (n := 0) (by simpa using hPclosed) ?_
    refine VExpr.ClosedN.mkApps_closed trivial fun arg harg => ?_
    have := hargs h hmem arg harg
    rw [hnparams h hmem] at this
    simpa using this

/-- No lambda replacement is a Pi type. -/
theorem Restoration.interpretation_preservesTelescopes (r : Restoration) (P : List VExpr) :
    (r.interpretation P).PreservesTelescopes :=
  fun _ _ hρ => Restoration.lambdaReplacement_ne_forallE r hρ

/-- An interpretation fixes a term none of whose constants and projection owners lie outside
the names it fixes. -/
theorem _root_.Lean4Lean.VEnv.Interpretation.expr_eq_self_of_avoid {I : Interpretation}
    {names : List Name} (hc : ∀ c, c ∉ names → I.consts c = none)
    (hr : ∀ c, c ∉ names → I.rename c = c) (hp : ∀ c, c ∉ names → I.projOwner c = c)
    (he : ∀ block owner, I.elim block owner = (block, owner)) :
    ∀ {e : VExpr}, e.containsAnyConst names = false → I.expr e = e
  | .bvar _, _ | .sort _, _ => rfl
  | .elim block owner ls, _ => by simp [Interpretation.expr, he]
  | .const c ls, h => by
    have hn : c ∉ names := by simpa [VExpr.containsAnyConst] using h
    rw [Interpretation.expr_const_none (hc c hn), hr c hn]
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Interpretation.expr, expr_eq_self_of_avoid hc hr hp he h.1,
      expr_eq_self_of_avoid hc hr hp he h.2]
  | .proj n i e, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    have hn : n ∉ names := by simpa using h.1
    simp only [Interpretation.expr, expr_eq_self_of_avoid hc hr hp he h.2, hp n hn]

/-- The restoration interpretation fixes a term avoiding the restorable names. -/
theorem Restoration.interpretation_expr_eq_self {r : Restoration} {P : List VExpr} {e : VExpr}
    (h : e.containsAnyConst r.restorableNames = false) : (r.interpretation P).expr e = e :=
  Interpretation.expr_eq_self_of_avoid
    (fun _ hc => Restoration.lambdaReplacement_eq_none_of_not_restorable hc)
    (fun _ hc => Restoration.renaming_eq_self hc) (fun _ hc => Restoration.renaming_eq_self hc)
    (fun _ _ => rfl) h

theorem Restoration.constInterpretation_expr_eq_self {r : Restoration} {P : List VExpr}
    {e : VExpr} (h : e.containsAnyConst r.restorableNames = false) :
    (r.constInterpretation P).expr e = e :=
  Interpretation.expr_eq_self_of_avoid
    (fun _ hc => Restoration.lambdaReplacement_eq_none_of_not_restorable hc)
    (fun _ hc => Restoration.renaming_eq_self hc) (fun _ _ => rfl) (fun _ _ => rfl) h

theorem Restoration.projNamesFixed_of_avoid {r : Restoration} :
    ∀ {e : VExpr}, e.projNamesAvoid r.restorableNames = true → e.ProjNamesFixed r.renaming
  | .bvar _, _ | .sort _, _ | .elim .., _ | .const .., _ => trivial
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true] at h
    exact ⟨projNamesFixed_of_avoid h.1, projNamesFixed_of_avoid h.2⟩
  | .proj n i e, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Restoration.renaming_eq_self (by simpa using h.1), projNamesFixed_of_avoid h.2⟩

/-! ### Agreement with restoration -/

/-- **Agreement** of the restoration `r` with the interpretation `I`: every interpreting term is
the parameter abstraction of a restoration head, every head is interpreted, away from the
heads the renaming is the recursor renaming, and eliminators are kept. -/
structure Restoration.Agrees (r : Restoration) (I : Interpretation) : Prop where
  /-- Every interpreting term is the parameter abstraction of a restoration head. -/
  shape : ∀ c t, I.consts c = some t → ∃ h doms,
    r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
    t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments)
  /-- Every restoration head is interpreted. -/
  headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → I.consts c ≠ none
  /-- Away from the heads, the renaming is the recursor renaming. -/
  renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none → I.rename c = r.recursorName c
  /-- Eliminators are kept. -/
  elim : ∀ block owner, I.elim block owner = (block, owner)
  /-- Restoration keeps projection owners, and so does the interpretation away from the
  restorable names. -/
  projOwner : ∀ n, n ∉ r.restorableNames → I.projOwner n = n

/-- Agreement does not read the projection-owner renaming beyond the non-restorable names. -/
theorem Restoration.Agrees.withProjOwner {r : Restoration} {I : Interpretation}
    (A : r.Agrees I) {σ : Name → Name} (hσ : ∀ n, n ∉ r.restorableNames → σ n = n) :
    r.Agrees { I with projOwner := σ } :=
  ⟨A.shape, A.headsReplaced, A.renamed, A.elim, hσ⟩

/-- The restoration interpretation agrees with the restoration. -/
theorem Restoration.interpretation_agrees {r : Restoration} {P : List VExpr}
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length) : r.Agrees (r.interpretation P) where
  shape c t hρ := Restoration.lambdaReplacement_shape r (fun h hmem => (hnparams h hmem).symm) hρ
  headsReplaced c h hf := by
    simp [Restoration.interpretation, Restoration.lambdaReplacement, hf]
  renamed c hf := Restoration.renaming_of_find_none hf
  elim _ _ := rfl
  projOwner _ hn := Restoration.renaming_eq_self hn

theorem Restoration.constInterpretation_agrees {r : Restoration} {P : List VExpr}
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length) : r.Agrees (r.constInterpretation P) :=
  (Restoration.interpretation_agrees hnparams).withProjOwner fun _ _ => rfl

/-- Agreement only reads the head lookup, the recursor renaming and the restorable names of the
restoration. -/
theorem Restoration.Agrees.congr {r r' : Restoration} {I : Interpretation} (A : r.Agrees I)
    (hfind : ∀ n, r.heads.find? (fun h => h.auxiliary == n) =
      r'.heads.find? (fun h => h.auxiliary == n))
    (hrec : ∀ n, r.recursorName n = r'.recursorName n)
    (hown : ∀ n, n ∉ r'.restorableNames → I.projOwner n = n) : r'.Agrees I where
  shape c t hρ := by
    obtain ⟨h, doms, hf, hlen, ht⟩ := A.shape c t hρ
    exact ⟨h, doms, (hfind c).symm.trans hf, hlen, ht⟩
  headsReplaced c h hf := A.headsReplaced c h ((hfind c).trans hf)
  renamed c hf := (A.renamed c ((hfind c).trans hf)).trans (hrec c)
  elim := A.elim
  projOwner := hown

/-- Projection owners avoiding the restorable names are fixed by an agreeing interpretation. -/
theorem Restoration.Agrees.projNamesFixed {r : Restoration} {I : Interpretation}
    (A : r.Agrees I) : ∀ {e : VExpr}, e.projNamesAvoid r.restorableNames = true →
      e.ProjNamesFixed I.projOwner
  | .bvar _, _ | .sort _, _ | .elim .., _ | .const .., _ => trivial
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true] at h
    exact ⟨A.projNamesFixed h.1, A.projNamesFixed h.2⟩
  | .proj n i e, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨A.projOwner n (by simpa using h.1), A.projNamesFixed h.2⟩

private theorem instantiateParams_eq_instOuter' (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Restoration is a beta reduct of an agreeing interpretation, for terms whose projection
owners the interpretation fixes. -/
theorem Restoration.Agrees.go_betaRed {r : Restoration} {I : Interpretation} (A : r.Agrees I) :
    ∀ (e : VExpr) {as as' : List VExpr} {out : VExpr},
      e.ProjNamesFixed I.projOwner → List.Forall₂ VExpr.BetaRed as as' →
      Restoration.expr.go r e as' = some out →
      VExpr.BetaRed (VExpr.mkApps (I.expr e) as) out := by
  intro e
  induction e with
  | bvar i =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact VExpr.BetaRed.mkApps .refl has
  | sort u =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact VExpr.BetaRed.mkApps .refl has
  | elim block owner ls =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    simp only [Interpretation.expr, A.elim]
    exact VExpr.BetaRed.mkApps .refl has
  | app fn arg ihfn iharg =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', harg, hfn⟩ := h
    have h1 := iharg (as := []) (as' := []) hfix.2 .nil harg
    exact ihfn (as := I.expr arg :: as) hfix.1 (.cons h1 has) hfn
  | lam d b ihd ihb =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact VExpr.BetaRed.mkApps (.lam (ihd (as := []) hfix.1 .nil hd)
      (ihb (as := []) hfix.2 .nil hb)) has
  | forallE d b ihd ihb =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact VExpr.BetaRed.mkApps (.forallE (ihd (as := []) hfix.1 .nil hd)
      (ihb (as := []) hfix.2 .nil hb)) has
  | proj n i m ih =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨m', hm, rfl⟩ := h
    simp only [Interpretation.expr, hfix.1]
    exact VExpr.BetaRed.mkApps (.proj (ih (as := []) hfix.2 .nil hm)) has
  | const c ls =>
    intro as as' out _ has h
    simp only [Restoration.expr.go] at h
    split at h
    · next hd hfind =>
      cases hρ : I.consts c with
      | none => exact absurd hρ (A.headsReplaced c hd hfind)
      | some t =>
        rw [Interpretation.expr_const_some hρ]
        obtain ⟨hd', doms, hfind', hdoms, rfl⟩ := A.shape c t hρ
        rw [hfind] at hfind'
        cases hfind'
        have hsim := VExpr.BetaRed.mkApps (f := (VExpr.wrapLams doms
          (VExpr.mkApps (.const hd.target hd.levels) hd.arguments)).instL ls) .refl has
        refine hsim.trans ?_
        unfold HeadSpecialization.apply at h
        split at h
        · cases h
        · next hlen =>
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
            Nat.not_lt] at hlen
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          rw [VExpr.instL_wrapLams]
          have := VExpr.BetaRed.mkApps_wrapLams (doms.map (VExpr.instL ls))
            ((VExpr.mkApps (.const hd.target hd.levels) hd.arguments).instL ls) as'
            (by simp [hdoms]; omega)
          simp only [List.length_map, hdoms] at this
          refine this.trans ?_
          simp only [VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps,
            VExpr.instOuter_const, ← VExpr.mkApps_append, List.map_map,
            Function.comp_def, instantiateParams_eq_instOuter']
          exact .refl
    · next hfind =>
      have hρ : I.consts c = none := by
        cases hρ : I.consts c with
        | none => rfl
        | some t =>
          obtain ⟨_, _, hfind', _⟩ := A.shape c t hρ
          rw [hfind] at hfind'
          cases hfind'
      simp only [Option.some.injEq] at h
      subst h
      rw [Interpretation.expr_const_none hρ, A.renamed c hfind]
      exact VExpr.BetaRed.mkApps .refl has

theorem Restoration.Agrees.expr_betaRed {r : Restoration} {I : Interpretation}
    (A : r.Agrees I) {e e' : VExpr} (hfix : e.ProjNamesFixed I.projOwner)
    (h : r.expr e = some e') : VExpr.BetaRed (I.expr e) e' :=
  A.go_betaRed e (as := []) hfix .nil h

/-- Restoration agrees with an agreeing interpretation up to beta, at every type of the
interpreted term, in a well-formed context. -/
theorem Restoration.Agrees.expr_simAt {r : Restoration} {I : Interpretation} {envS : VEnv}
    (A : r.Agrees I) (henv : envS.Ordered) (hβ : envS.BetaSubjectReduction U)
    (hΓ : OnCtx Γ (envS.IsType U)) {e e' : VExpr} (hfix : e.ProjNamesFixed I.projOwner)
    (h : r.expr e = some e') : envS.SimAt U Γ (I.expr e) e' :=
  (A.expr_betaRed hfix h).simAt henv hβ hΓ

/-! ### Restoration substitutions -/

/-- A sound interpretation of `envL` in `envS`, for well-formed contexts, agreeing with the
restoration `r`. -/
structure Restoration.Substitution (envS envL : VEnv) (r : Restoration) (I : Interpretation) :
    Prop where
  sound : I.Sound envS envL envS.TypedCtx
  agrees : r.Agrees I

theorem Restoration.Substitution.ordered {envS envL : VEnv} {r : Restoration}
    {I : Interpretation} (S : r.Substitution envS envL I) : envS.Ordered :=
  S.sound.ordered

theorem Restoration.Substitution.expr_simAt {envS envL : VEnv} {r : Restoration}
    {I : Interpretation} (S : r.Substitution envS envL I) (hβ : envS.BetaSubjectReduction U)
    (hΓ : OnCtx Γ (envS.IsType U)) {e e' : VExpr} (hfix : e.ProjNamesFixed I.projOwner)
    (h : r.expr e = some e') : envS.SimAt U Γ (I.expr e) e' :=
  S.agrees.expr_simAt S.ordered hβ hΓ hfix h

/-- Restoration of a closed typing judgment of `envL`. -/
theorem Restoration.expr_hasType {envS envL : VEnv} {r : Restoration} {I : Interpretation}
    (S : r.Substitution envS envL I) (hβ : envS.BetaSubjectReduction U)
    {e A e' A' : VExpr} (H : envL.HasType U [] e A) (he : r.expr e = some e')
    (hA : r.expr A = some A') (hfix : e.ProjNamesFixed I.projOwner)
    (hfixA : A.ProjNamesFixed I.projOwner) :
    envS.HasType U [] e' A' := by
  have henv := S.ordered
  have HI : envS.HasType U [] (I.expr e) (I.expr A) :=
    S.sound.hasType (.typed henv) H trivial
  have h1 := S.expr_simAt hβ (Γ := []) trivial hfix he _ HI
  obtain ⟨u, hAI⟩ := VEnv.IsDefEq.isType henv (Γ := []) trivial HI
  have h3 := S.expr_simAt hβ (Γ := []) trivial hfixA hA _ hAI
  exact .defeqDF h3 (h1.symm.trans (HI.trans h1))

/-- Restoration of a well-formed closed equation of `envL`. -/
theorem Restoration.equation_wf {envS envL : VEnv} {r : Restoration} {I : Interpretation}
    (S : r.Substitution envS envL I) {df df' : VDefEq}
    (hβ : envS.BetaSubjectReduction df.uvars) (hwf : df.WF envL)
    (hfixL : df.lhs.ProjNamesFixed I.projOwner) (hfixR : df.rhs.ProjNamesFixed I.projOwner)
    (hfixT : df.type.ProjNamesFixed I.projOwner) (h : r.equation df = some df') :
    df'.WF envS := by
  simp only [Restoration.equation, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨l, hl, rr, hr, t, ht, rfl⟩ := h
  exact ⟨Restoration.expr_hasType S hβ hwf.1 hl ht hfixL hfixT,
    Restoration.expr_hasType S hβ hwf.2 hr ht hfixR hfixT⟩

/-- Restoration of a closed definitional equality of `envL`, without restoring the type. -/
theorem Restoration.expr_isDefEqU {envS envL : VEnv} {r : Restoration} {I : Interpretation}
    (S : r.Substitution envS envL I) (hβ : envS.BetaSubjectReduction U)
    (H : envL.IsDefEqU U [] e₁ e₂) (he₁ : r.expr e₁ = some e₁')
    (he₂ : r.expr e₂ = some e₂') (hfix₁ : e₁.ProjNamesFixed I.projOwner)
    (hfix₂ : e₂.ProjNamesFixed I.projOwner) :
    envS.IsDefEqU U [] e₁' e₂' := by
  obtain ⟨_, H⟩ := H
  have HI := S.sound.isDefEq (.typed S.ordered) H trivial
  have h1 := S.expr_simAt hβ (Γ := []) trivial hfix₁ he₁ _ HI.hasType.1
  have h2 := S.expr_simAt hβ (Γ := []) trivial hfix₂ he₂ _ HI.hasType.2
  exact ⟨_, h1.symm.trans (HI.trans h2)⟩

/-- A type restored from a type definitionally equal, in `envL`, to one that restores to a term
definitionally equal (at every type) to the source type. -/
theorem RestoresType.of_models_constructor {envS envL : VEnv} {r : Restoration}
    {I : Interpretation} {uvars : Nat} (S : r.Substitution envS envL I)
    (hβ : envS.BetaSubjectReduction uvars)
    (hdefeq : envL.IsDefEqU uvars [] normalized expandedType)
    (hrestored : r.expr expandedType = some restoredExpanded)
    (hsource : envS.SimAt uvars [] restoredExpanded sourceType)
    (hnorm : ∃ restored, r.expr normalized = some restored)
    (hfixN : normalized.ProjNamesFixed I.projOwner)
    (hfixE : expandedType.ProjNamesFixed I.projOwner) :
    RestoresType r envS uvars normalized sourceType := by
  obtain ⟨restored, hn⟩ := hnorm
  obtain ⟨_, h1⟩ := Restoration.expr_isDefEqU S hβ hdefeq hn hrestored hfixN hfixE
  exact ⟨restored, hn, _, h1.trans (hsource _ h1.hasType.2)⟩

end InductiveSignature

/-! ### Restored eliminators -/

/-- A schema with the same signature as `schema` is `schema` with its source
families and restoration replaced. -/
theorem InductiveSignature.CaseSchema.eq_with_of_signature
    {schema schemaS : InductiveSignature.CaseSchema} (h : schemaS.signature = schema.signature) :
    schemaS = { schema with
      sourceFamilies := schemaS.sourceFamilies
      restoration := schemaS.restoration } := by
  cases schemaS
  cases h
  rfl

/-- The generic type of the restored schema is the restoration of the generic
type of the restoration-free schema. -/
theorem InductiveSignature.CaseSchema.genericType_withRestoration
    {schema : InductiveSignature.CaseSchema} (h0 : schema.restoration = {})
    {owner : Fin schema.signature.families.size} {type : VExpr}
    (h : schema.genericType owner = some type) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).genericType owner =
      r.expr type := by
  simp only [InductiveSignature.CaseSchema.genericType, InductiveSignature.CaseSchema.type,
    h0, InductiveSignature.Restoration.expr_empty, Option.some.injEq] at h ⊢
  rw [← h]
  rfl

/-- The generic equations of the restored schema are the restorations of the
generic equations of the restoration-free schema. -/
theorem InductiveSignature.CaseSchema.genericEquations_withRestoration
    {schema : InductiveSignature.CaseSchema} (h0 : schema.restoration = {}) {block : Name}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (h : schema.genericEquations block owner = some rules) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).genericEquations block owner = rules.mapM r.equation := by
  have hempty : (({} : InductiveSignature.Restoration).equation) = fun e => some e := by
    funext e
    exact InductiveSignature.Restoration.equation_empty e
  simp only [InductiveSignature.CaseSchema.genericEquations,
    InductiveSignature.CaseSchema.equations, h0, hempty] at h ⊢
  have hsome : ∀ l : List VDefEq, l.mapM (fun e => some e) = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.mapM_cons, ih]
  rw [hsome] at h
  cases h
  rfl

/-- `Permission` only reads the signature. -/
theorem InductiveSignature.CaseSchema.Permission.withRestoration
    {schema : InductiveSignature.CaseSchema} {owner : Fin schema.signature.families.size}
    {U : Nat} {levels : List VLevel} {target : VLevel}
    (H : schema.Permission U owner levels target) (families : List Name)
    (r : InductiveSignature.Restoration) :
    ({ schema with sourceFamilies := families, restoration := r } :
      InductiveSignature.CaseSchema).Permission U owner levels target :=
  ⟨H.length, H.levels_wf, H.target_wf, H.admissible⟩

namespace VEnv

open InductiveSignature

/-- A restoration-free eliminator `(block, schema)` of the source environment of `I`, matched
in `envS` by the registered schema with the same signature, the source families `families` and
the restoration `r`, which agrees with `I` (`CaseSchema.eq_with_of_signature` puts a source
schema with the same signature in this form). Its rules hold after interpretation in
well-formed contexts (`RestoredEliminator.clause`), through the agreement of restoration with
`I` up to beta, which needs beta subject reduction in `envS`, the projection owners of the
generic type and equations fixed by `I`, and their restorations to succeed. -/
structure RestoredEliminator (envS : VEnv) (I : Interpretation) (block : Name)
    (schema : CaseSchema) (families : List Name) (r : Restoration) : Prop where
  /-- The source schema carries no restoration. -/
  restorationFree : schema.restoration = {}
  /-- The restored schema, with the same signature, the source families `families` and the
  restoration `r`, is registered under the same key. -/
  registered : envS.eliminators block
    { schema with sourceFamilies := families, restoration := r }
  /-- The restoration agrees with the interpretation. -/
  agrees : r.Agrees I
  /-- The restoration table is scoped (the head arguments are closed under the
  head parameters, so restoration preserves closedness). -/
  restorationScoped : r.Scoped
  betaSubjectReduction : ∀ U, envS.BetaSubjectReduction U
  /-- The generic type has its projection owners fixed and is restorable. -/
  genericType : ∀ owner type, schema.genericType owner = some type →
    type.ProjNamesFixed I.projOwner ∧ (r.expr type).isSome
  /-- The generic equations have their projection owners fixed and are restorable. -/
  genericEquations : ∀ owner rules, schema.genericEquations block owner = some rules →
    ∀ df ∈ rules, df.lhs.ProjNamesFixed I.projOwner ∧ df.rhs.ProjNamesFixed I.projOwner ∧
      df.type.ProjNamesFixed I.projOwner ∧ (r.equation df).isSome

private theorem restoredEliminator_closedN {r : Restoration}
    (hr : r.Scoped) {e e' : VExpr} (he : e.Closed) (h : r.expr e = some e') : e'.Closed :=
  EnvTables.restore_go_closedN r (fun h hh a ha => (hr.2.2.1 h hh).2 a ha) e [] 0 e' he
    (by simp) h

private theorem restoredEliminator_instL {r : Restoration} {e e' : VExpr}
    (h : r.expr e = some e') (ls : List VLevel) :
    r.expr (e.instL ls) = some (e'.instL ls) := by
  rw [← Restoration.expr_instL, h]
  rfl

private theorem mapM_equation_of_isSome (r : Restoration) :
    ∀ {l : List VDefEq}, (∀ d ∈ l, (r.equation d).isSome) → ∃ l', l.mapM r.equation = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    obtain ⟨l', hl⟩ := mapM_equation_of_isSome r (l := l)
      (fun d hd => h d (List.mem_cons_of_mem _ hd))
    exact ⟨a' :: l', by simp [List.mapM_cons, ha, hl]⟩

/-- **The eliminator clause of a restored eliminator**, in well-formed contexts: the congruence
rule through the registered restored schema, and the iota rule through its restored rule. -/
theorem RestoredEliminator.clause {envS : VEnv} {I : Interpretation} {block : Name}
    {schema : CaseSchema} {families : List Name} {r : Restoration}
    (R : RestoredEliminator envS I block schema families r) (henv : envS.Ordered) :
    I.EliminatorClause envS envS.TypedCtx block schema where
  elimDF := by
    intro owner type U Γ levels levels' target target' typeLevel hΓ htype hclosed hperm
      hright heq htyped
    obtain ⟨hfixT, hsome⟩ := R.genericType owner type htype
    obtain ⟨type', htype'⟩ := Option.isSome_iff_exists.mp hsome
    have hgen := CaseSchema.genericType_withRestoration R.restorationFree htype families r
    rw [htype'] at hgen
    have hdef := R.agrees.expr_simAt henv (R.betaSubjectReduction U) hΓ hfixT.instL
      (restoredEliminator_instL htype' (target :: levels)) _ htyped
    have hS := VEnv.IsDefEq.elimDF
      (schema := { schema with sourceFamilies := families, restoration := r }) (owner := owner)
      R.registered hgen (restoredEliminator_closedN R.restorationScoped hclosed htype')
      (hperm.withRestoration families r) hright heq hdef.hasType.2
    simp only [Interpretation.expr_elim, R.agrees.elim]
    exact .defeqDF hdef.symm hS
  elimIota := by
    intro owner rules df U Γ levels target hΓ hgen hmem hclosed hperm hleft hright
    obtain ⟨hfixL, hfixR, hfixT, hsome⟩ := R.genericEquations owner rules hgen df hmem
    obtain ⟨df', hdf'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨rules', hrules'⟩ := mapM_equation_of_isSome r
      (fun d hd => (R.genericEquations owner rules hgen d hd).2.2.2)
    have hgen' := CaseSchema.genericEquations_withRestoration R.restorationFree hgen families r
    rw [hrules'] at hgen'
    have hmem' : df' ∈ rules' := by
      obtain ⟨d, hd, hdd⟩ :=
        List.Forall₂.forall_exists_l (List.mapM_eq_some.mp hrules') df hmem
      rw [hdf'] at hdd
      cases hdd
      exact hd
    obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hdf'
    have hclosed' : CaseSchema.RuleClosed df' :=
      ⟨restoredEliminator_closedN R.restorationScoped hclosed.1 hl,
        restoredEliminator_closedN R.restorationScoped hclosed.2.1 hr,
        restoredEliminator_closedN R.restorationScoped hclosed.2.2 ht⟩
    have hβ := R.betaSubjectReduction U
    have hL := R.agrees.expr_simAt henv hβ hΓ hfixL.instL
      (restoredEliminator_instL hl (target :: levels)) _ hleft
    have hR := R.agrees.expr_simAt henv hβ hΓ hfixR.instL
      (restoredEliminator_instL hr (target :: levels)) _ hright
    obtain ⟨u, hT⟩ := hleft.isType henv hΓ
    have hTT := R.agrees.expr_simAt henv hβ hΓ hfixT.instL
      (restoredEliminator_instL ht (target :: levels)) _ hT
    have hι := VEnv.IsDefEq.elimIota
      (schema := { schema with sourceFamilies := families, restoration := r })
      (owner := owner) R.registered hgen' hmem' hclosed' (hperm.withRestoration families r)
      (.defeqDF hTT hL.hasType.2) (.defeqDF hTT hR.hasType.2)
    exact hL.trans ((VEnv.IsDefEq.defeqDF hTT.symm hι).trans hR.symm)

/-- A restored eliminator in a well-formed target environment: beta subject reduction, the
scope of the restoration and the restorability of the generic types follow from
well-formedness. -/
theorem RestoredEliminator.of_wf {envS : VEnv} {I : Interpretation} {block : Name}
    {schema : CaseSchema} {families : List Name} {r : Restoration} (hS : envS.WF)
    (h0 : schema.restoration = {})
    (hreg : envS.eliminators block
      { schema with sourceFamilies := families, restoration := r })
    (A : r.Agrees I)
    (htype : ∀ owner type, schema.genericType owner = some type →
      type.ProjNamesFixed I.projOwner)
    (heqs : ∀ owner rules, schema.genericEquations block owner = some rules →
      ∀ df ∈ rules, df.lhs.ProjNamesFixed I.projOwner ∧ df.rhs.ProjNamesFixed I.projOwner ∧
        df.type.ProjNamesFixed I.projOwner ∧ (r.equation df).isSome) :
    RestoredEliminator envS I block schema families r where
  restorationFree := h0
  registered := hreg
  agrees := A
  restorationScoped := VEnv.WF.eliminator_restoration_scoped hS hreg
  betaSubjectReduction _ := hS.betaSubjectReduction
  genericType owner type h := by
    refine ⟨htype owner type h, ?_⟩
    obtain ⟨type', h', -⟩ := EnvTables.VEnv.WF.eliminator_genericType_closed hS hreg owner
    rw [CaseSchema.genericType_withRestoration h0 h families r] at h'
    rw [h']
    rfl
  genericEquations := heqs

end VEnv
end Lean4Lean
