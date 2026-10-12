import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Typing.ProjectionRigidity
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Quot

/-!
# Recursor and quotient facts carried through a checking environment

Recursor reduction is the ι pattern rule (`IsDefEq.pat`): the rule the checker fires is read off
the environment translation (`TrEnv.pats_iota'`), so no alignment of recursors with stored
equations is carried here. What remains is what the checker's major-premise conversions and
quotient reduction read:

* the K clause (`KLikeRecursor`): a K-like recursor eliminates from a proposition with a single
  constructor whose only arguments are the parameters (`toCtorWhenK`);
* the major inductive of every recursor is an inductive header of the map;
* the heads of the reduction rules (`EquationHeadsCoherent`): every stored equation is headed by
  a non-inductive constant of the map, other than `Quot`, and every registered pattern by a
  recursor of the map. Rigidity of inductive type constants and of `Quot` follows;
* the quotient constants and the `Quot.lift` equation (`QuotCoherent`).

The K clause and the major inductives are facts about installed blocks
(`InstalledBlocks.recursorEnvCoherent`); the rule heads and the quotient facts are read off the
translation (`TrEnv'.equationHeads`, `TrEnv'.quotEnvCoherent`).
-/

namespace Lean4Lean
open Lean

/-- A K-like recursor eliminates from a proposition with a single constructor whose only
arguments are the parameters. Stored headers and constructor types may require reduction
to expose these telescopes (for example, a header ending in `id Prop`). The constructor's
parameter binders agree with the inductive's binders by typed equality. -/
def KLikeAlignment (venv : VEnv) (rec : RecursorVal) (ctorName : Name) : Prop :=
  ∃ indUvars indType ctorType indDoms ctorDoms ctorBody,
    venv.constants rec.getMajorInduct = some ⟨indUvars, indType⟩ ∧
    venv.IsDefEqU indUvars [] indType (VExpr.wrapForalls indDoms (.sort .zero)) ∧
    indDoms.length = rec.numParams + rec.numIndices ∧
    venv.constants ctorName = some ⟨indUvars, ctorType⟩ ∧
    venv.IsDefEqU indUvars [] ctorType (VExpr.wrapForalls ctorDoms ctorBody) ∧
    ctorDoms.length = rec.numParams ∧
    ∀ k (hk : k < indDoms.length) (hk' : k < ctorDoms.length),
      venv.IsDefEqU indUvars ((indDoms.take k).reverse) indDoms[k] ctorDoms[k]

/-- The K clause for one recursor: when the recursor is K-like, its major inductive is a
single-constructor family of `C` whose constructor is aligned. -/
def KLikeRecursor (C : ConstMap) (venv : VEnv) (rec : RecursorVal) : Prop :=
  rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
    info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName

/-- Every visible recursor of the constant map satisfies the K clause. -/
def RecursorRulesCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) → safety ≤ (ConstantInfo.recInfo rec).safety →
    KLikeRecursor C venv rec

/-- The quotient constants and the `Quot.lift` equation are present, and `Quot` is rigid. -/
structure QuotCoherent (venv : VEnv) : Prop where
  quot : venv.constants ``Quot = some quotConst
  quotMk : venv.constants ``Quot.mk = some quotMkConst
  lift : venv.constants ``Quot.lift = some quotLiftConst
  ind : venv.constants ``Quot.ind = some quotIndConst
  defeq : venv.defeqs quotDefEq
  rigid : venv.Rigid ``Quot

/-- The kind of equation head the invariant admits: a non-inductive constant of `C`, and not a
quotient constant other than `Quot.lift`. -/
def EquationHeadOf (C : ConstMap) (df : VDefEq) : Prop :=
  ∃ head ls ci, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
    C.find? head = some ci ∧ (∀ info, ci ≠ .inductInfo info) ∧
    (∀ q, ci = .quotInfo q → q.kind = .lift)

/-- The heads of the reduction rules: every stored equation is headed by an admissible constant
of `C` (`EquationHeadOf`), and every registered pattern by a recursor of `C`. Rigidity of
inductive type constants and of `Quot` follows (`rigid`, `rigid_quot`). -/
structure EquationHeadsCoherent (C : ConstMap) (venv : VEnv) : Prop where
  defeqs : ∀ df, venv.defeqs df → EquationHeadOf C df
  pats : ∀ p r, venv.pats p r → ∃ rec, C.find? p.headConst = some (.recInfo rec)

/-- The recursor facts carried through a checking environment: every visible recursor satisfies
the K clause, its major inductive is an inductive type of the map, and the reduction rules are
headed by admissible constants of the map. -/
structure RecursorEnvCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) :
    Prop where
  rules : RecursorRulesCoherent safety C venv
  majors : ∀ {name rec}, C.find? name = some (.recInfo rec) →
    safety ≤ (ConstantInfo.recInfo rec).safety →
    ∃ info, C.find? rec.getMajorInduct = some (.inductInfo info)
  heads : EquationHeadsCoherent C venv

/-- The quotient facts carried through a checking environment: the abstract quotient constants
and equation, together with the kernel entry of `Quot` (which is what keeps `Quot` rigid along
the translation). -/
structure QuotEnvCoherent (C : ConstMap) (venv : VEnv) : Prop where
  coherent : QuotCoherent venv
  find : ∃ q : QuotVal, C.find? ``Quot = some (.quotInfo q) ∧ q.kind = .type

variable {venv venv' : VEnv}

theorem VEnv.addDefEqs_defeqs_iff : ∀ {cis : List VDefVal} {env : VEnv} {df : VDefEq},
    (env.addDefEqs cis).defeqs df ↔ env.defeqs df ∨ ∃ ci ∈ cis, df = ci.toDefEq
  | [], _, _ => by simp [VEnv.addDefEqs]
  | ci :: cis, env, df => by
    show (VEnv.addDefEqs (env.addDefEq ci.toDefEq) cis).defeqs df ↔ _
    rw [VEnv.addDefEqs_defeqs_iff]
    simp only [VEnv.addDefEq, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

/-! ## Monotonicity -/

theorem KLikeAlignment.mono (h : venv ≤ venv')
    (H : KLikeAlignment venv rec ctorName) : KLikeAlignment venv' rec ctorName := by
  obtain ⟨indUvars, indType, ctorType, indDoms, ctorDoms, ctorBody,
    hI, hInorm, hIlen, hC, hCnorm, hClen, hparams⟩ := H
  refine ⟨indUvars, indType, ctorType, indDoms, ctorDoms, ctorBody,
    h.constants hI, hInorm.mono h, hIlen, h.constants hC, hCnorm.mono h, hClen, ?_⟩
  intro k hk hk'
  exact (hparams k hk hk').mono h

theorem KLikeRecursor.mono {C C' : ConstMap} (h : venv ≤ venv')
    (hC : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (H : KLikeRecursor C venv rec) : KLikeRecursor C' venv' rec := fun hk =>
  let ⟨info, ctorName, hfind, hctors, halign⟩ := H hk
  ⟨info, ctorName, hC hfind, hctors, halign.mono h⟩

theorem QuotCoherent.mono_of_rigid (h : venv ≤ venv') (hr : venv'.Rigid ``Quot)
    (H : QuotCoherent venv) : QuotCoherent venv' where
  quot := h.constants H.quot
  quotMk := h.constants H.quotMk
  lift := h.constants H.lift
  ind := h.constants H.ind
  defeq := h.defeqs H.defeq
  rigid := hr

/-! ## Rigidity from the rule heads -/

theorem EquationHeadsCoherent.rigid {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? n = some (.inductInfo info)) : venv.Rigid n where
  defeqs df hdf ls heq := by
    obtain ⟨head, ls', ci, hhead, hci, hne, -⟩ := H.defeqs df hdf
    rw [heq] at hhead
    cases hhead
    rw [h] at hci
    exact hne info (Option.some.inj hci).symm
  pats p r hp heq := by
    obtain ⟨rec, hrec⟩ := H.pats p r hp
    rw [heq, h] at hrec
    cases hrec

theorem EquationHeadsCoherent.rigid_quot {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? ``Quot = some (.quotInfo q)) (hk : q.kind = .type) : venv.Rigid ``Quot where
  defeqs df hdf ls heq := by
    obtain ⟨head, ls', ci, hhead, hci, -, hq⟩ := H.defeqs df hdf
    rw [heq] at hhead
    cases hhead
    rw [h] at hci
    have := hq q (Option.some.inj hci).symm
    rw [hk] at this
    cases this
  pats p r hp heq := by
    obtain ⟨rec, hrec⟩ := H.pats p r hp
    rw [heq, h] at hrec
    cases hrec

/-- A constant absent from the map heads no reduction rule. -/
theorem EquationHeadsCoherent.rigid_of_fresh {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? n = none) : venv.Rigid n where
  defeqs df hdf ls heq := by
    obtain ⟨head, ls', ci, hhead, hci, -, -⟩ := H.defeqs df hdf
    rw [heq] at hhead
    cases hhead
    rw [h] at hci
    cases hci
  pats p r hp heq := by
    obtain ⟨rec, hrec⟩ := H.pats p r hp
    rw [heq, h] at hrec
    cases hrec

/-! ## Transport of the rule heads

Every step of the environment translation preserves the map's lookups and adds rules headed
by admissible constants of the target map; `EquationHeadsCoherent.extend` covers all of them. -/

theorem EquationHeadOf.ofDefn {C : ConstMap} {df : VDefEq}
    (h : ∃ head ls d, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
      C.find? head = some (.defnInfo d)) : EquationHeadOf C df :=
  let ⟨head, ls, _, hhead, hfind⟩ := h
  ⟨head, ls, _, hhead, hfind, nofun, nofun⟩

theorem EquationHeadOf.mono {C C' : ConstMap} {df : VDefEq}
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (H : EquationHeadOf C df) : EquationHeadOf C' df :=
  let ⟨head, ls, ci, hhead, hci, hne, hq⟩ := H
  ⟨head, ls, ci, hhead, hpres hci, hne, hq⟩

/-- The head of a definition's delta rule is the definition constant. -/
theorem VDefVal.toDefEq_head (v : VDefVal) :
    v.toDefEq.lhs.stripLams.getAppFnArgs.1 = .const v.name (VLevel.params v.uvars) := rfl

/-- The master transport lemma for the rule heads. -/
theorem EquationHeadsCoherent.extend {C C' : ConstMap}
    (H : EquationHeadsCoherent C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df ∨ EquationHeadOf C' df)
    (hpats : ∀ p r, venv'.pats p r →
      venv.pats p r ∨ ∃ rec, C'.find? p.headConst = some (.recInfo rec)) :
    EquationHeadsCoherent C' venv' where
  defeqs df hdf := (hdefeq df hdf).elim (fun h => (H.defeqs df h).mono hpres) id
  pats p r hp := (hpats p r hp).elim (fun h => let ⟨rec, hr⟩ := H.pats p r h; ⟨rec, hpres hr⟩) id

/-- Transport along a step that adds no rule. -/
theorem EquationHeadsCoherent.extendSimple {C C' : ConstMap}
    (H : EquationHeadsCoherent C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df)
    (hpats : ∀ p r, venv'.pats p r → venv.pats p r) :
    EquationHeadsCoherent C' venv' :=
  H.extend hpres (fun df h => .inl (hdefeq df h)) (fun p r h => .inl (hpats p r h))

theorem EquationHeadsCoherent.insert {C : ConstMap}
    (H : EquationHeadsCoherent C venv) (hwf : C.WF) (hfresh : C.find? n = none)
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df)
    (hpats : ∀ p r, venv'.pats p r → venv.pats p r) :
    EquationHeadsCoherent (C.insert n ci) venv' :=
  H.extendSimple (fun h => SMap.find?_insert_of_fresh hwf.map₂ hfresh h) hdefeq hpats

theorem EquationHeadsCoherent.addDefEq {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (hhead : EquationHeadOf C df) : EquationHeadsCoherent C (venv.addDefEq df) :=
  H.extend id (fun _ hdf' => hdf'.elim (fun h => .inr (h ▸ hhead)) .inl)
    (fun _ _ h => .inl h)

theorem EquationHeadsCoherent.addProjections {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (entries : List VProjectionEntry) :
    EquationHeadsCoherent C (venv.addProjections entries) :=
  H.extendSimple id (fun df h => by rwa [VEnv.addProjections_defeqs] at h)
    (fun p r h => by rwa [VEnv.addProjections_pats] at h)

theorem QuotEnvCoherent.extend {C C' : ConstMap} (H : QuotEnvCoherent C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hle : venv ≤ venv') (hheads : EquationHeadsCoherent C' venv') :
    QuotEnvCoherent C' venv' :=
  let ⟨q, hq, hk⟩ := H.find
  ⟨H.coherent.mono_of_rigid hle (hheads.rigid_quot (hpres hq) hk), q, hpres hq, hk⟩

end Lean4Lean
