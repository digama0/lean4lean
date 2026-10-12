import Lean4Lean.Theory.VDecl

/-! # The staged extension `VEnv.addInduct` and the recursor data of a compiled block

The stages of `VEnv.addInduct` (type formers, constructors, projections, recursors, ι rules)
and the syntactic reading of a declaration's recursors off a compiled block
(`VRecRule.OfEquation`, `VInductDecl.RecsOf`). They live below `Theory/Inductive.lean` so
that `Theory/Inductive/Compilation.lean` can phrase the installation of a prior container
(`ContainersInstalled`) on `addInduct`. -/

namespace Lean4Lean

/-- Register recursor rule `ru` (of recursor `r`) as an ι rule: redex `r`'s spine (major
at `getMajorIdx`) applied to `ru.ctor`'s spine (`ctorParams + nfields` arguments),
reduct `SimplePattern.iotaRHS`. Fails if `ru.rhs` is not closed. Only the constructor
rule of thesis §2.6.4 is registered: K-like reduction (its second rule, on a
non-constructor major of a subsingleton eliminator) is not registered — see
`VInductDecl.WF`. -/
def VEnv.addRecRule (env : VEnv) (r : VRecursor) (ru : VRecRule) : Option VEnv :=
  if h : ru.rhs.Closed then
    some <| env.addPat
      (SimplePattern.iota r.name (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs h,
        .true)
  else none

/-! ### The stages of `addInduct`

The kernel (`Inductive/Add.lean`, `run`) declares all type formers, then all constructors
(in block order), then each recursor *together with its rules* (`mkRecRules` inside the
per-recursor loop, installed in one `recInfo`); for a nested block `Environment.addInductive`
inserts type by type (`Verify/Environment/Basic.lean`, `AddInduct.consts`). The model
re-groups this into five stages — all type formers, all constructors, the projection entries
of the block's structures, all recursors, then all ι rules — which yields the same resulting
environment as the kernel's interleaving, not its literal order. Each stage is
named so that `VInductDecl.WF` can type each kind of constant in the environment the kernel
checks it in. -/

/-- Stage 0: add the type formers as constants. -/
def VInductDecl.addTypes (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.types.foldlM (init := env) fun e t => e.addConst t.name t.toVConstVal.toVConstant

/-- Stage 1: add the constructors of every type former, in block order. -/
def VInductDecl.addCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.types.flatMap (·.ctors)).foldlM (init := env) fun e c => e.addConst c.name c.toVConstant

/-- Stage 2: register the projection entries of the declaration's structures
(`VInductDecl.projectionEntries`). Total: projection registration cannot fail. The recursors
are checked in the resulting environment, where the block's structures already have their
projections (the checker may apply `structEta`, `unitLike` or project out of them while
checking the generated recursor types). -/
def VInductDecl.addProjs (decl : VInductDecl) (env : VEnv) : VEnv :=
  env.addProjections decl.projectionEntries

/-- Stage 3: add the recursors as constants. -/
def VInductDecl.addRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r => e.addConst r.name r.toVConstVal.toVConstant

/-- Stage 4: register every recursor rule as an ι rule. -/
def VInductDecl.addRules (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru

/-- Stages 0–1: the constructor environment. -/
def VInductDecl.addTypesCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypes env >>= decl.addCtors

/-- Stages 0–2: the environment the recursors are checked in. -/
def VInductDecl.addTypesCtorsProjs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.addTypesCtors env).map decl.addProjs

/-- Stages 0–3: the environment the ι rules are registered in. -/
def VInductDecl.addTypesCtorsProjsRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypesCtorsProjs env >>= decl.addRecs

/-- The constants of the declaration as `(name, constant)` pairs, in stage order (type
formers, constructors, recursors): the constant stages are the `addConst` fold over this list
(`VInductDecl.addTypesCtorsProjsRecs_eq`). -/
def VInductDecl.consts (decl : VInductDecl) : List (Name × VConstant) :=
  decl.types.map (fun t => (t.name, t.toVConstVal.toVConstant)) ++
  (decl.types.flatMap (·.ctors)).map (fun c => (c.name, c.toVConstant)) ++
  decl.recs.map (fun r => (r.name, r.toVConstVal.toVConstant))

/-- Extend `env` with the type formers, constructors, and recursors of `decl` (as
constants), the projection entries of its structures (as `projections`) and its
ι-reduction rules (as `pats`), or `none` on a name clash or a non-closed rule reduct. The
chain of `VInductDecl.addTypes`, `addCtors`, `addProjs`, `addRecs`, `addRules`. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.addTypesCtorsProjsRecs env >>= decl.addRules


/-- Stage 0 of `addInduct` is `addConstVals` over the type constants. -/
theorem VInductDecl.addTypes_eq_addConstVals (decl : VInductDecl) (env : VEnv) :
    decl.addTypes env = env.addConstVals decl.typeConstants := by
  unfold VInductDecl.addTypes VInductDecl.typeConstants
  induction decl.types generalizing env with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldlM_cons, List.map_cons, VEnv.addConstVals]
    cases env.addConst t.name t.toVConstVal.toVConstant <;> simp [ih]

/-- Stage 1 of `addInduct` is `addConstVals` over the constructor constants. -/
theorem VInductDecl.addCtors_eq_addConstVals (decl : VInductDecl) (env : VEnv) :
    decl.addCtors env = env.addConstVals decl.constructorConstants := by
  unfold VInductDecl.addCtors VInductDecl.constructorConstants
  generalize decl.types.flatMap (·.ctors) = cs
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldlM_cons, VEnv.addConstVals]
    cases env.addConst c.name c.toVConstant <;> simp [ih]


/-- `decl.recs` is read off a compiled block: the recursor constants are the block's
generated recursors, in order, and each recursor rule is the block's generated equation
for that recursor and constructor, reduct for reduct (`VRecRule.OfEquation`). -/
def VRecRule.OfEquation (r : VRecursor) (ru : VRecRule) (df : VDefEq) : Prop :=
  df.rhs = ru.rhs ∧
  df.lhs.lamBody.headConst? = some r.name ∧
  df.lhs.lamBody.getAppArgs.length = r.getMajorIdx + 1 ∧
  ∃ major, df.lhs.lamBody.getAppArgs.getLast? = some major ∧
    major.headConst? = some ru.ctor ∧
    major.getAppArgs.length = ru.ctorParams + ru.nfields

/-- The recursor data of a declaration against a compiled block: the recursor constants are
the block's, and the rules are in bijection with the block's generated equations. -/
structure VInductDecl.RecsOf (decl : VInductDecl) (block : VInductBlock) : Prop where
  recursors : decl.recs.map (·.toVConstVal) = block.recursors
  rules : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ df ∈ block.rules, VRecRule.OfEquation r ru df
  rules_total : ∀ df ∈ block.rules, ∃ r ∈ decl.recs, ∃ ru ∈ r.rules, VRecRule.OfEquation r ru df

/-! ### Replaying the stages over a larger environment

A successful stage of `addInduct` replays over any larger environment in which its names are
fresh, above the original result. -/

namespace VEnv

theorem addPat_mono {env₁ env₂ : VEnv} {p : Pattern} {r : p.RHS × p.Check} (H : env₁ ≤ env₂) :
    env₁.addPat p r ≤ env₂.addPat p r where
  constants := H.constants
  defeqs := H.defeqs
  pats h := h.elim .inl (.inr ∘ H.pats)
  projections := H.projections

/-- A fold whose steps replay over larger environments replays as a whole. -/
theorem foldlM_rebase {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e₁ e₂ e₁' : VEnv} {x}, e₁ ≤ e₂ → f e₁ x = some e₁' →
      ∃ e₂', f e₂ x = some e₂' ∧ e₁' ≤ e₂') :
    ∀ {l : List α} {i₁ i₂ o₁ : VEnv}, i₁ ≤ i₂ → l.foldlM f i₁ = some o₁ →
      ∃ o₂, l.foldlM f i₂ = some o₂ ∧ o₁ ≤ o₂
  | [], i₁, i₂, o₁, hle, h => by simp [List.foldlM] at h; subst h; exact ⟨i₂, rfl, hle⟩
  | x :: xs, i₁, i₂, o₁, hle, h => by
    simp only [List.foldlM] at h
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e2, h1', hle'⟩ := hf hle h1
    obtain ⟨o₂, h2', hle''⟩ := foldlM_rebase (f := f) hf hle' h2
    exact ⟨o₂, by simp only [List.foldlM, h1']; exact h2', hle''⟩

/-- A fold whose successful steps are monotone in the environment is monotone. -/
theorem foldlM_mono {α} {f : VEnv → α → Option VEnv}
    (hf : ∀ {e₁ e₂ e₁' e₂' : VEnv} {x}, e₁ ≤ e₂ → f e₁ x = some e₁' → f e₂ x = some e₂' →
      e₁' ≤ e₂') :
    ∀ {l : List α} {i₁ i₂ o₁ o₂ : VEnv}, i₁ ≤ i₂ → l.foldlM f i₁ = some o₁ →
      l.foldlM f i₂ = some o₂ → o₁ ≤ o₂
  | [], _, _, _, _, hle, h, h' => by
    simp [List.foldlM] at h h'; subst h h'; exact hle
  | x :: xs, _, _, _, _, hle, h, h' => by
    simp only [List.foldlM] at h h'
    obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e1', h1', h2'⟩ := Option.bind_eq_some_iff.1 h'
    exact foldlM_mono (f := f) hf (hf hle h1 h1') h2 h2'

theorem addRecRule_rebase {e₁ e₂ e₁' : VEnv} {r : VRecursor} {ru : VRecRule} (hle : e₁ ≤ e₂)
    (h : e₁.addRecRule r ru = some e₁') :
    ∃ e₂', e₂.addRecRule r ru = some e₂' ∧ e₁' ≤ e₂' := by
  unfold VEnv.addRecRule at h ⊢
  split at h
  · cases h; rw [dif_pos ‹_›]; exact ⟨_, rfl, addPat_mono hle⟩
  · cases h

theorem addRules_rebase {decl : VInductDecl} {e₁ e₂ e₁' : VEnv} (hle : e₁ ≤ e₂)
    (h : decl.addRules e₁ = some e₁') :
    ∃ e₂', decl.addRules e₂ = some e₂' ∧ e₁' ≤ e₂' := by
  unfold VInductDecl.addRules at h ⊢
  exact foldlM_rebase (f := fun e r => r.rules.foldlM (fun e ru => e.addRecRule r ru) e)
    (fun {_ _ _ r} hle h => foldlM_rebase (f := fun e ru => VEnv.addRecRule e r ru)
      (fun hle h => addRecRule_rebase hle h) hle h) hle h

theorem addRules_mono {decl : VInductDecl} {e₁ e₂ e₁' e₂' : VEnv} (hle : e₁ ≤ e₂)
    (h : decl.addRules e₁ = some e₁') (h' : decl.addRules e₂ = some e₂') : e₁' ≤ e₂' := by
  obtain ⟨e₂'', h'', hle'⟩ := addRules_rebase hle h
  rw [h'] at h''; cases h''; exact hle'

/-- The constant stages of `addInduct`, as the one fold over `VInductDecl.consts`. -/
theorem addTypesCtorsProjsRecs_of_stages {decl : VInductDecl} {env envT envC envR : VEnv}
    (stT : decl.addTypes env = some envT) (stC : decl.addCtors envT = some envC)
    (stR : decl.addRecs (decl.addProjs envC) = some envR) :
    decl.addTypesCtorsProjsRecs env = some envR := by
  simp [VInductDecl.addTypesCtorsProjsRecs, VInductDecl.addTypesCtorsProjs,
    VInductDecl.addTypesCtors, stT, stC, stR]

theorem stages_of_addTypesCtorsProjsRecs {decl : VInductDecl} {env envR : VEnv}
    (h : decl.addTypesCtorsProjsRecs env = some envR) :
    ∃ envT envC, decl.addTypes env = some envT ∧ decl.addCtors envT = some envC ∧
      decl.addRecs (decl.addProjs envC) = some envR := by
  unfold VInductDecl.addTypesCtorsProjsRecs at h
  obtain ⟨envP, hP', hRec⟩ := Option.bind_eq_some_iff.1 h
  unfold VInductDecl.addTypesCtorsProjs at hP'
  obtain ⟨envC, hC', rfl⟩ := Option.map_eq_some_iff.1 hP'
  unfold VInductDecl.addTypesCtors at hC'
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 hC'
  exact ⟨envT, envC, hT, hC, hRec⟩

theorem foldlM_exists {α} {f : VEnv → α → Option VEnv} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ e, ∃ e', f e x = some e') → ∀ init, ∃ r, l.foldlM f init = some r
  | [], _, init => ⟨init, rfl⟩
  | x :: xs, hf, init => by
    obtain ⟨e1, h1⟩ := hf x (.head _) init
    obtain ⟨r, hr⟩ := foldlM_exists (fun y hy => hf y (.tail _ hy)) e1
    exact ⟨r, by simp only [List.foldlM, h1]; exact hr⟩

/-- The ι-rule stage succeeds once every reduct is closed. -/
theorem addRules_exists {decl : VInductDecl} (env : VEnv)
    (h : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed) : ∃ env', decl.addRules env = some env' := by
  unfold VInductDecl.addRules
  exact foldlM_exists (fun r hr e => foldlM_exists (f := fun e ru => VEnv.addRecRule e r ru)
    (fun ru hru e => ⟨_, by unfold VEnv.addRecRule; rw [dif_pos (h r hr ru hru)]⟩) e) env

end VEnv

end Lean4Lean
