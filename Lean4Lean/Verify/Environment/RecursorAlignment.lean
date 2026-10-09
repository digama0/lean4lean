import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Quot
import Lean4Lean.Std.SMap

/-!
# Recursor rules as a checking invariant: the predicates

The executable checker reduces a recursor application by looking up the `RecursorRule` for the
constructor at the head of the major premise. The abstract environment stores each such rule as a
closed lambda-wrapped equation. This file states, for a checking environment, that every visible
recursor's rules are stored equations of the shape `VIotaRuleShape`, that the recursor's type and
each constructor's type have the shapes `VRecursorShape` and `VConstructorShape`, that the major
inductive type constant is rigid, and (for K-like recursors) that the inductive type is a
proposition whose parameters type the unique constructor. The quotient reduction rules are covered
by the same shapes for `Quot.lift`, and by proof irrelevance for `Quot.ind`.

The predicates are carried along the environment translation (`TrEnv'`) and through the checking
invariant (`CheckingEnv.Valid`); the transport lemmas at the end of this file are what every step
of the translation uses. The inductive installation boundary (`AddInduct`) records the facts about
the recursors it installs as `NewRecursorsAligned`.
-/

namespace Lean4Lean
open Lean

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

/-- The stored equation `df` is the iota rule of `rec` for `rule`: it has the rule shape, its
right-hand side translates the executable rule's right-hand side, and the rule's constructor has
the constructor shape at `cnparams` parameters. -/
structure RecursorRuleAlignment (venv : VEnv) (rec : RecursorVal) (rule : RecursorRule)
    (indLevels : List VLevel) (cnparams : Nat) (ctorParams : List VExpr)
    (df : VDefEq) : Prop where
  shape : Nonempty (VIotaRuleShape venv rec.name rec.levelParams.length rec.numParams cnparams
    rec.numMotives rec.numMinors rec.numIndices rule.ctor indLevels rule.nfields df ctorParams)
  rhs : TrExprS venv rec.levelParams [] rule.rhs df.rhs
  ctor : ∃ ctorUvars, indLevels.length = ctorUvars ∧
    Nonempty (VConstructorShape venv rule.ctor ctorUvars cnparams rule.nfields rec.numIndices
      rec.getMajorInduct)

/-- The recursor's major type and all its rules share a scoped constructor
parameter substitution. The constructor parameter count is existential and
need not agree with `rec.numParams`. Its major family is rigid. -/
def RecursorAlignment (venv : VEnv) (rec : RecursorVal) : Prop :=
  ∃ cnparams indLevels ctorParams,
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
      rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels ctorParams) ∧
    venv.Rigid rec.getMajorInduct ∧
    ∀ rule ∈ rec.rules, ∃ df, RecursorRuleAlignment venv rec rule indLevels cnparams ctorParams df

/-- `RecursorAlignment` without its rigidity clause: the part that is monotone in the abstract
environment. Rigidity of the major inductive is recovered from the heads of the stored equations
(`EquationHeadsCoherent`). -/
def RecursorAlignmentCore (venv : VEnv) (rec : RecursorVal) : Prop :=
  ∃ cnparams indLevels ctorParams,
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
      rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels ctorParams) ∧
    ∀ rule ∈ rec.rules, ∃ df, RecursorRuleAlignment venv rec rule indLevels cnparams ctorParams df

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

/-- The K clause of `RecursorRulesCoherent` for one recursor: when the recursor is K-like, its
major inductive is a single-constructor family of `C` whose constructor is aligned. -/
def KLikeRecursor (C : ConstMap) (venv : VEnv) (rec : RecursorVal) : Prop :=
  rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
    info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName

/-- Every visible recursor of the constant map is aligned with the abstract environment. -/
def RecursorRulesCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) → safety ≤ (ConstantInfo.recInfo rec).safety →
    RecursorAlignment venv rec ∧
    (rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
      info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName)

/-- The quotient constants and the `Quot.lift` equation are present, and `Quot` is rigid. -/
structure QuotCoherent (venv : VEnv) : Prop where
  quot : venv.constants ``Quot = some quotConst
  quotMk : venv.constants ``Quot.mk = some quotMkConst
  lift : venv.constants ``Quot.lift = some quotLiftConst
  ind : venv.constants ``Quot.ind = some quotIndConst
  defeq : venv.defeqs quotDefEq
  rigid : venv.Rigid ``Quot

/-- Every stored equation is headed by a constant of `C` that is neither an inductive type nor a
quotient constant other than `Quot.lift`. Rigidity of inductive type constants and of `Quot`
follows from this global property of the environment. -/
def EquationHeadsCoherent (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ df, venv.defeqs df → ∃ head ls ci, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
    C.find? head = some ci ∧ (∀ info, ci ≠ .inductInfo info) ∧
    (∀ q, ci = .quotInfo q → q.kind = .lift)

/-- The recursor facts carried through a checking environment: every visible recursor is aligned,
its major inductive is an inductive type of the map, and every stored equation is headed by a
non-inductive constant of the map. -/
structure RecursorEnvCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) :
    Prop where
  rules : RecursorRulesCoherent safety C venv
  majors : ∀ {name rec}, C.find? name = some (.recInfo rec) →
    safety ≤ (ConstantInfo.recInfo rec).safety →
    ∃ info, C.find? rec.getMajorInduct = some (.inductInfo info)
  heads : EquationHeadsCoherent C venv

/-- The quotient facts carried through a checking environment: the abstract quotient constants and
equation, together with the kernel entry of `Quot` (which is what keeps `Quot` rigid along
the translation). -/
structure QuotEnvCoherent (C : ConstMap) (venv : VEnv) : Prop where
  coherent : QuotCoherent venv
  find : ∃ q : QuotVal, C.find? ``Quot = some (.quotInfo q) ∧ q.kind = .type

/-- What an inductive installation certifies about the recursors it installs: every recursor of
the target map is either already in the source map or aligned in the target environment (with a
K clause and an inductive major), and every new stored equation is headed by a recursor of the target map. -/
structure NewRecursorsAligned (safety : DefinitionSafety)
    (m₁ : ConstMap) (env₁ : VEnv) (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  recursor : ∀ {name rec}, m₂.find? name = some (.recInfo rec) →
    m₁.find? name = some (.recInfo rec) ∨
    (safety ≤ (ConstantInfo.recInfo rec).safety →
      RecursorAlignmentCore env₂ rec ∧ KLikeRecursor m₂ env₂ rec ∧
      ∃ info, m₂.find? rec.getMajorInduct = some (.inductInfo info))
  defeq : ∀ df, env₂.defeqs df → env₁.defeqs df ∨
    ∃ head ls rec, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
      m₂.find? head = some (.recInfo rec)

variable {venv venv' : VEnv}

/-! ## Rigidity -/

/-- Adding an equation headed (under its lambdas) by a constant that is not `c` keeps `c` rigid. -/
theorem VEnv.Rigid.addDefEq (hc : venv.Rigid c)
    (hhead : ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c ls) :
    (venv.addDefEq df).Rigid c := by
  intro df' hdf' ls
  rcases hdf' with rfl | hdf'
  · exact hhead ls
  · exact hc df' hdf' ls

theorem VEnv.addDefEqRules_defeqs_iff : ∀ {dfs : List VDefEq} {env : VEnv} {df : VDefEq},
    (env.addDefEqRules dfs).defeqs df ↔ env.defeqs df ∨ df ∈ dfs
  | [], _, _ => by simp [VEnv.addDefEqRules]
  | rule :: dfs, env, df => by
    show (VEnv.addDefEqRules (env.addDefEq rule) dfs).defeqs df ↔ _
    rw [VEnv.addDefEqRules_defeqs_iff]
    simp only [VEnv.addDefEq, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

theorem VEnv.addConsts_defeqs : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | [], _, _, h => by cases h; rfl
  | ci :: cis, env, env', h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h₁, h₂⟩ := h
    rw [VEnv.addConsts_defeqs (cis := cis) h₂, VEnv.addConst_defeqs h₁]

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

/-! ## Monotonicity

The shape invariants only look up constants and stored equations, so they are preserved by
environment extension. Rigidity is not: it is preserved exactly when the new stored equations are
headed elsewhere, so the rigidity clauses are re-established from the heads of the stored
equations (`EquationHeadsCoherent`). -/

def VRecursorShape.mono (h : venv ≤ venv')
    (H : VRecursorShape venv recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams) :
    VRecursorShape venv' recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams :=
  { H with const := h.constants H.const }

def VConstructorShape.mono (h : venv ≤ venv')
    (H : VConstructorShape venv ctorName ctorUvars nparams nfields nindices indName) :
    VConstructorShape venv' ctorName ctorUvars nparams nfields nindices indName :=
  { H with const := h.constants H.const }

/-- A rule shape survives environment extension once its recursor and constructor are already
present, since the domain-agreement fields are stated for the constants' actual types. -/
def VIotaRuleShape.mono (h : venv ≤ venv')
    (hrec : ∃ ci, venv.constants recName = some ci)
    (hctor : ∃ ci, venv.constants ctorName = some ci)
    (H : VIotaRuleShape venv recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams) :
    VIotaRuleShape venv' recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams :=
  { H with
    defeq := h.defeqs H.defeq
    rec_doms := fun recDoms recBody hc hlen => by
      obtain ⟨ci, hci⟩ := hrec
      rw [h.constants hci] at hc
      cases hc
      exact H.rec_doms recDoms recBody hci hlen
    ctor_doms := fun ctorUvars ctorDoms ctorBody hc hlen i hi hd hcd => by
      obtain ⟨ci, hci⟩ := hctor
      rw [h.constants hci] at hc
      cases hc
      exact (H.ctor_doms ctorUvars ctorDoms ctorBody hci hlen i hi hd hcd).mono h }

theorem RecursorRuleAlignment.mono {rec : RecursorVal} (h : venv ≤ venv')
    (hrec : ∃ ci, venv.constants rec.name = some ci)
    (H : RecursorRuleAlignment venv rec rule indLevels cnparams ctorParams df) :
    RecursorRuleAlignment venv' rec rule indLevels cnparams ctorParams df where
  shape := H.ctor.elim fun _ ⟨_, hs⟩ => hs.elim fun c =>
    H.shape.elim fun s => ⟨s.mono h hrec ⟨_, c.const⟩⟩
  rhs := H.rhs.mono h
  ctor := H.ctor.elim fun u ⟨hu, hs⟩ => ⟨u, hu, hs.elim fun s => ⟨s.mono h⟩⟩

theorem RecursorAlignmentCore.mono (h : venv ≤ venv')
    (H : RecursorAlignmentCore venv rec) : RecursorAlignmentCore venv' rec :=
  let ⟨cnparams, indLevels, ctorParams, ⟨s⟩, hrules⟩ := H
  ⟨cnparams, indLevels, ctorParams, ⟨s.mono h⟩, fun rule hrule =>
    let ⟨df, hdf⟩ := hrules rule hrule; ⟨df, hdf.mono h ⟨_, s.const⟩⟩⟩

theorem RecursorAlignment.core (H : RecursorAlignment venv rec) :
    RecursorAlignmentCore venv rec :=
  let ⟨cnparams, indLevels, ctorParams, hs, _, hrules⟩ := H
  ⟨cnparams, indLevels, ctorParams, hs, hrules⟩

theorem RecursorAlignmentCore.toAlignment (H : RecursorAlignmentCore venv rec)
    (hrigid : venv.Rigid rec.getMajorInduct) : RecursorAlignment venv rec :=
  let ⟨cnparams, indLevels, ctorParams, hs, hrules⟩ := H
  ⟨cnparams, indLevels, ctorParams, hs, hrigid, hrules⟩

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

/-! ## Heads of stored equations -/

theorem EquationHeadsCoherent.rigid {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? n = some (.inductInfo info)) : venv.Rigid n := by
  intro df hdf ls heq
  obtain ⟨head, ls', ci, hhead, hci, hne, -⟩ := H df hdf
  rw [heq] at hhead
  cases hhead
  rw [h] at hci
  exact hne info (Option.some.inj hci).symm

theorem EquationHeadsCoherent.rigid_quot {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? ``Quot = some (.quotInfo q)) (hk : q.kind = .type) : venv.Rigid ``Quot := by
  intro df hdf ls heq
  obtain ⟨head, ls', ci, hhead, hci, -, hq⟩ := H df hdf
  rw [heq] at hhead
  cases hhead
  rw [h] at hci
  have := hq q (Option.some.inj hci).symm
  rw [hk] at this
  cases this

/-- A constant absent from the map heads no stored equation. -/
theorem EquationHeadsCoherent.rigid_of_fresh {C : ConstMap} (H : EquationHeadsCoherent C venv)
    (h : C.find? n = none) : venv.Rigid n := by
  intro df hdf ls heq
  obtain ⟨head, ls', ci, hhead, hci, -, -⟩ := H df hdf
  rw [heq] at hhead
  cases hhead
  rw [h] at hci
  cases hci

/-! ## Transport of the carried facts

Every step of the environment translation preserves the map's lookups, may add constants, and adds
equations that are headed by non-inductive constants of the target map. The master lemma
`RecursorEnvCoherent.extend` covers all of them; the specialized forms below are what the
translation steps call. -/

/-- The kind of equation head that keeps the invariant: a non-inductive constant of `C`, and not a
quotient constant other than `Quot.lift`. -/
def EquationHeadOf (C : ConstMap) (df : VDefEq) : Prop :=
  ∃ head ls ci, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
    C.find? head = some ci ∧ (∀ info, ci ≠ .inductInfo info) ∧
    (∀ q, ci = .quotInfo q → q.kind = .lift)

theorem EquationHeadOf.ofRecursor {C : ConstMap} {df : VDefEq}
    (h : ∃ head ls rec, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
      C.find? head = some (.recInfo rec)) : EquationHeadOf C df :=
  let ⟨head, ls, _, hhead, hfind⟩ := h
  ⟨head, ls, _, hhead, hfind, nofun, nofun⟩

theorem EquationHeadOf.ofDefn {C : ConstMap} {df : VDefEq}
    (h : ∃ head ls d, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
      C.find? head = some (.defnInfo d)) : EquationHeadOf C df :=
  let ⟨head, ls, _, hhead, hfind⟩ := h
  ⟨head, ls, _, hhead, hfind, nofun, nofun⟩

/-- The head of a definition's delta rule is the definition constant. -/
theorem VDefVal.toDefEq_head (v : VDefVal) :
    v.toDefEq.lhs.stripLams.getAppFnArgs.1 = .const v.name (VLevel.params v.uvars) := rfl

/-- The master transport lemma: lookups of `C` are preserved in `C'`, every visible recursor of
`C'` is old or comes with its alignment, the abstract environment grows, and every new stored
equation is headed by an acceptable constant of `C'`. -/
theorem RecursorEnvCoherent.extend {C C' : ConstMap}
    (H : RecursorEnvCoherent safety C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hrec : ∀ {n rec}, C'.find? n = some (.recInfo rec) →
      safety ≤ (ConstantInfo.recInfo rec).safety →
      C.find? n = some (.recInfo rec) ∨
      (RecursorAlignmentCore venv' rec ∧ KLikeRecursor C' venv' rec ∧
        ∃ info, C'.find? rec.getMajorInduct = some (.inductInfo info)))
    (hle : venv ≤ venv')
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df ∨ EquationHeadOf C' df) :
    RecursorEnvCoherent safety C' venv' := by
  have heads : EquationHeadsCoherent C' venv' := by
    intro df hdf
    rcases hdefeq df hdf with hold | hnew
    · obtain ⟨head, ls, ci, hhead, hci, hne, hq⟩ := H.heads df hold
      exact ⟨head, ls, ci, hhead, hpres hci, hne, hq⟩
    · exact hnew
  refine ⟨?_, ?_, heads⟩
  · intro name rec hfind hsafe
    rcases hrec hfind hsafe with hold | ⟨hcore, hk, info, hmajor⟩
    · obtain ⟨halign, hK⟩ := H.rules hold hsafe
      obtain ⟨info, hmajor⟩ := H.majors hold hsafe
      refine ⟨(halign.core.mono hle).toAlignment (heads.rigid (hpres hmajor)), ?_⟩
      intro hk
      obtain ⟨info', ctorName, hfind', hctors, hKL⟩ := hK hk
      exact ⟨info', ctorName, hpres hfind', hctors, hKL.mono hle⟩
    · exact ⟨hcore.toAlignment (heads.rigid hmajor), hk⟩
  · intro name rec hfind hsafe
    rcases hrec hfind hsafe with hold | ⟨-, -, hmajor⟩
    · obtain ⟨info, hmajor⟩ := H.majors hold hsafe
      exact ⟨info, hpres hmajor⟩
    · exact hmajor

/-- Transport along a step that adds no recursor and no equation. -/
theorem RecursorEnvCoherent.extendSimple {C C' : ConstMap}
    (H : RecursorEnvCoherent safety C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hrec : ∀ {n rec}, C'.find? n = some (.recInfo rec) →
      safety ≤ (ConstantInfo.recInfo rec).safety → C.find? n = some (.recInfo rec))
    (hle : venv ≤ venv')
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df) :
    RecursorEnvCoherent safety C' venv' :=
  H.extend hpres (fun h hs => .inl (hrec h hs)) hle fun df hdf => .inl (hdefeq df hdf)

theorem RecursorEnvCoherent.addProjections {C : ConstMap} (H : RecursorEnvCoherent safety C venv)
    (entries : List VProjectionEntry) :
    RecursorEnvCoherent safety C (venv.addProjections entries) :=
  H.extendSimple (fun h => h) (fun h _ => h) VEnv.addProjections_le fun df hdf => by
    rwa [VEnv.addProjections_defeqs] at hdf

/-- Inserting a fresh constant into the map and adding its abstract counterpart, when the constant
is not a recursor. -/
theorem RecursorEnvCoherent.insertNonRecursor {C : ConstMap}
    (H : RecursorEnvCoherent safety C venv) (hwf : C.WF) (hfresh : C.find? n = none)
    (hnrec : ∀ rec, ci ≠ .recInfo rec) (hle : venv ≤ venv')
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df) :
    RecursorEnvCoherent safety (C.insert n ci) venv' := by
  refine H.extendSimple ?_ ?_ hle hdefeq
  · intro m ci' hm
    rw [hwf.find?_insert]
    split
    · rename_i heq; rw [beq_iff_eq] at heq; subst heq; rw [hfresh] at hm; cases hm
    · exact hm
  · intro m rec hm _
    rw [hwf.find?_insert] at hm
    split at hm
    · exact absurd (Option.some.inj hm) (hnrec rec)
    · exact hm

/-- Inserting a constant invisible at this safety. -/
theorem RecursorEnvCoherent.insertInvisible {C : ConstMap}
    (H : RecursorEnvCoherent safety C venv) (hwf : C.WF) (hfresh : C.find? n = none)
    (hinvisible : ¬ safety ≤ ci.safety) :
    RecursorEnvCoherent safety (C.insert n ci) venv := by
  refine H.extendSimple ?_ ?_ VEnv.LE.rfl fun _ h => h
  · intro m ci' hm
    rw [hwf.find?_insert]
    split
    · rename_i heq; rw [beq_iff_eq] at heq; subst heq; rw [hfresh] at hm; cases hm
    · exact hm
  · intro m rec hm hs
    rw [hwf.find?_insert] at hm
    split at hm
    · cases Option.some.inj hm; exact absurd hs hinvisible
    · exact hm

/-- Adding an equation headed by an acceptable constant of `C`. -/
theorem RecursorEnvCoherent.addDefEq {C : ConstMap} (H : RecursorEnvCoherent safety C venv)
    (hhead : EquationHeadOf C df) : RecursorEnvCoherent safety C (venv.addDefEq df) :=
  H.extend (fun h => h) (fun h _ => .inl h) VEnv.addDefEq_le fun df' hdf' => by
    rcases hdf' with rfl | hdf'
    · exact .inr hhead
    · exact .inl hdf'

/-- What installing the constant `ci` into a checking environment must certify about recursors:
nothing unless `ci` is a recursor, in which case its alignment in the extended abstract
environment `venv'`, the K clause over the map before the insertion, and its inductive major. -/
def RecursorInstallStep (safety : DefinitionSafety) (C : ConstMap) (venv' : VEnv) :
    ConstantInfo → Prop
  | .recInfo rec => safety ≤ (ConstantInfo.recInfo rec).safety →
    RecursorAlignmentCore venv' rec ∧ KLikeRecursor C venv' rec ∧
    ∃ info, C.find? rec.getMajorInduct = some (.inductInfo info)
  | _ => True

theorem RecursorInstallStep.of_not_rec {C : ConstMap} {ci : ConstantInfo}
    (h : ∀ rec, ci ≠ .recInfo rec) : RecursorInstallStep safety C venv' ci := by
  cases ci <;> first | trivial | exact absurd rfl (h _)

/-- Inserting a fresh constant into the map and adding its abstract counterpart, with the
recursor obligation of the step. -/
theorem RecursorEnvCoherent.insert {C : ConstMap}
    (H : RecursorEnvCoherent safety C venv) (hwf : C.WF) (hfresh : C.find? n = none)
    (hstep : RecursorInstallStep safety C venv' ci) (hle : venv ≤ venv')
    (hdefeq : ∀ df, venv'.defeqs df → venv.defeqs df) :
    RecursorEnvCoherent safety (C.insert n ci) venv' := by
  have hpres : ∀ {m ci'}, C.find? m = some ci' → (C.insert n ci).find? m = some ci' := by
    intro m ci' hm
    rw [hwf.find?_insert]
    split
    · rename_i heq; rw [beq_iff_eq] at heq; subst heq; rw [hfresh] at hm; cases hm
    · exact hm
  refine H.extend hpres ?_ hle fun df hdf => .inl (hdefeq df hdf)
  intro m rec hm hs
  rw [hwf.find?_insert] at hm
  split at hm
  · cases Option.some.inj hm
    obtain ⟨hcore, hk, info, hmajor⟩ := hstep hs
    exact .inr ⟨hcore, hk.mono VEnv.LE.rfl hpres, info, hpres hmajor⟩
  · exact .inl hm

/-- The inductive installation step. -/
theorem RecursorEnvCoherent.addInduct {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    (H : RecursorEnvCoherent safety m₁ env₁)
    (P : NewRecursorsAligned safety m₁ env₁ m₂ env₂)
    (hpres : ∀ {n ci}, m₁.find? n = some ci → m₂.find? n = some ci)
    (hle : env₁ ≤ env₂) : RecursorEnvCoherent safety m₂ env₂ :=
  H.extend hpres (fun h hs => (P.recursor h).imp id fun h' => h' hs) hle fun df hdf =>
    (P.defeq df hdf).imp id EquationHeadOf.ofRecursor

theorem QuotEnvCoherent.extend {C C' : ConstMap} (H : QuotEnvCoherent C venv)
    (hpres : ∀ {n ci}, C.find? n = some ci → C'.find? n = some ci)
    (hle : venv ≤ venv') (hheads : EquationHeadsCoherent C' venv') :
    QuotEnvCoherent C' venv' :=
  let ⟨q, hq, hk⟩ := H.find
  ⟨H.coherent.mono_of_rigid hle (hheads.rigid_quot (hpres hq) hk), q, hpres hq, hk⟩

/-- Rebase an installation certificate to larger environments that add the same equations. -/
theorem NewRecursorsAligned.mono {m₁ m₂ : ConstMap} {env₁ env₂ env₁' env₂' : VEnv}
    (P : NewRecursorsAligned safety m₁ env₁ m₂ env₂)
    (hle₁ : env₁ ≤ env₁') (hle₂ : env₂ ≤ env₂')
    (hdefeq : ∀ df, env₂'.defeqs df → env₁'.defeqs df ∨ env₂.defeqs df) :
    NewRecursorsAligned safety m₁ env₁' m₂ env₂' where
  recursor h := (P.recursor h).imp id fun h' hs =>
    let ⟨hcore, hk, hmajor⟩ := h' hs
    ⟨hcore.mono hle₂, hk.mono hle₂ id, hmajor⟩
  defeq df hdf := by
    rcases hdefeq df hdf with h | h
    · exact .inl h
    · exact (P.defeq df h).imp hle₁.defeqs id

/-- Installing a block adds exactly its generated equations to the source. -/
theorem VInductBlock.install_defeqs_iff
    {env out : VEnv} {block : VInductBlock}
    (h : block.install env = some out) (df : VDefEq) :
    out.defeqs df ↔ env.defeqs df ∨ df ∈ block.rules := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  rcases h with ⟨envTypes, ht, envCtors, hc, envRecs, hr, rfl⟩
  rw [VEnv.addDefEqRules_defeqs_iff, VEnv.addConstVals_defeqs hr,
    VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs, VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht]

theorem NewRecursorsAligned.ofUnsafe
    (H : NewRecursorsAligned .unsafe source base target out) :
    NewRecursorsAligned safety source base target out where
  recursor h := (H.recursor h).imp id (fun h _ => h DefinitionSafety.unsafe_le)
  defeq := H.defeq

theorem NewRecursorsAligned.rebaseBlock
    {block block' : VInductBlock}
    (H : NewRecursorsAligned safety source base target out)
    (hbase : base ≤ base') (hout : out ≤ out')
    (hi : block.install base = some out)
    (hi' : block'.install base' = some out')
    (hrules : block.rules = block'.rules) :
    NewRecursorsAligned safety source base' target out' := by
  apply H.mono hbase hout
  intro df hd
  rcases (VInductBlock.install_defeqs_iff hi' df).mp hd with h | h
  · exact .inl h
  · exact .inr ((VInductBlock.install_defeqs_iff hi df).mpr (.inr (hrules ▸ h)))
end Lean4Lean
