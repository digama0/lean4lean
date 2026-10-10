import Lean4Lean.Theory.Typing.Strong

/-! # Environment interpretations

An interpretation `I : VEnv.Interpretation` maps the syntax of a source environment `envL`
into a target environment `envS`:

* a constant `c` is either interpreted by a closed universe-polymorphic term `t`
  (`I.consts c = some t`; the occurrence `.const c ls` becomes `t.instL ls`, possibly an
  application: restoration interprets an auxiliary family by `λ params, J levels args` and an
  auxiliary constructor by `λ params, J.c levels args`), or renamed (`I.rename`);
* projection owners are renamed (`I.projOwner`).

`I.expr` applies the interpretation to an expression. `I.Sound envS envL P` collects the
obligations: every interpreting term is closed (`Interpretation.Closed`, so that interpretation
commutes with substitution); each interpreted constant has the interpretation of its type up to
definitional equality (`ConstClause`); each definitional axiom holds after interpretation
(`DefEqClause`); and the ι rules (`PatClause`) and projection rules (`ProjectionClause`) hold
after interpretation in every target context satisfying the context invariant `P`.

**Transport** (`Interpretation.Sound.isDefEq`): for every context invariant `P` closed under the
context extensions made by the typing rules (`VEnv.CtxInvariant`), a sound interpretation maps
every derivation of `envL` whose interpreted context satisfies `P` to a derivation of `envS`.
Two invariants are used. `fun _ _ => True` gives the context-free transport, for
interpretations whose rules hold in arbitrary contexts; `VEnv.TypedCtx` (well-formed contexts)
admits rules that are only transported up to beta subject reduction, which needs a
well-formed context (the restored ι rules and the projections of auxiliary structure-like
families of `Theory/Inductive/RestorationInterpretation.lean`). A sound interpretation for an
invariant is sound for every stronger one (`Sound.weaken`).

Closure is separate from shape: that no interpreting term is a Pi type
(`Interpretation.PreservesTelescopes`) is needed only where a projection field type is computed by
walking a constructor telescope (`fieldType_interpret`, `ProjectionClause.of_fixed`).

WAVE 3 COMPAT (port of the source branch's file): the eliminator clause is gone with
`VExpr.elim`; its place is taken by `PatClause`, the obligation for a registered ι rule
(`IsDefEq.pat`, PORT_PLAN section 3). `PatClause.of_fixed` discharges it for a rule of `envS`
whose constants and fixed reduct terms the interpretation fixes (the analogue of
`DefEqClause.of_rule`); the restored rules of a nested block are the `RestoredPattern`s of
`RestorationInterpretation.lean`. -/

namespace Lean4Lean

/-- An interpretation of the constants and projection owners of one environment in another
(see the module documentation). -/
structure VEnv.Interpretation where
  /-- Constants interpreted by closed universe-polymorphic terms. -/
  consts : Name → Option VExpr
  /-- The renaming of every other constant. -/
  rename : Name → Name
  /-- The renaming of projection owners. -/
  projOwner : Name → Name := rename

/-- Every projection owner of the term is fixed by `σ`. -/
def VExpr.ProjNamesFixed (σ : Name → Name) : VExpr → Prop
  | .bvar _ | .sort _ | .const .. => True
  | .app f a | .lam f a | .forallE f a => f.ProjNamesFixed σ ∧ a.ProjNamesFixed σ
  | .proj n _ e => σ n = n ∧ e.ProjNamesFixed σ

/-- Universe instantiation does not touch projection owners. -/
theorem VExpr.ProjNamesFixed.instL {σ : Name → Name} {ls : List VLevel} :
    ∀ {e : VExpr}, e.ProjNamesFixed σ → (e.instL ls).ProjNamesFixed σ
  | .bvar _, _ | .sort _, _ | .const .., _ => trivial
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => ⟨instL h.1, instL h.2⟩
  | .proj _ _ _, h => ⟨h.1, instL h.2⟩

theorem VExpr.projNamesFixed_id : ∀ e : VExpr, e.ProjNamesFixed id
  | .bvar _ | .sort _ | .const .. => trivial
  | .app f a | .lam f a | .forallE f a => ⟨projNamesFixed_id f, projNamesFixed_id a⟩
  | .proj _ _ e => ⟨rfl, projNamesFixed_id e⟩

namespace VEnv.Interpretation

/-- The interpretation of an expression. -/
def expr (I : Interpretation) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls =>
    match I.consts c with
    | some t => t.instL ls
    | none => .const (I.rename c) ls
  | .app f a => .app (expr I f) (expr I a)
  | .proj n i e => .proj (I.projOwner n) i (expr I e)
  | .lam A b => .lam (expr I A) (expr I b)
  | .forallE A b => .forallE (expr I A) (expr I b)

variable (I : Interpretation)

/-- Every interpreting term is closed. -/
def Closed : Prop := ∀ c t, I.consts c = some t → t.ClosedN

/-- No interpreting term is a Pi type, so interpretation does not lengthen a telescope. -/
def PreservesTelescopes : Prop := ∀ c t, I.consts c = some t → ∀ A B, t ≠ .forallE A B

variable {I}

theorem expr_const_some {c : Name} {t : VExpr} {ls : List VLevel} (h : I.consts c = some t) :
    I.expr (.const c ls) = t.instL ls := by
  simp [expr, h]

theorem expr_const_none {c : Name} {ls : List VLevel} (h : I.consts c = none) :
    I.expr (.const c ls) = .const (I.rename c) ls := by
  simp [expr, h]

theorem expr_proj {n : Name} {i : Nat} {e : VExpr} :
    I.expr (.proj n i e) = .proj (I.projOwner n) i (I.expr e) := rfl

@[simp] theorem expr_mkApps (f : VExpr) (args : List VExpr) :
    I.expr (VExpr.mkApps f args) = VExpr.mkApps (I.expr f) (args.map I.expr) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem expr_liftN (hI : I.Closed) (e : VExpr) (n k : Nat) :
    I.expr (e.liftN n k) = (I.expr e).liftN n k := by
  induction e generalizing k with
  | bvar | sort => rfl
  | const c ls =>
    simp only [VExpr.liftN, expr]
    split
    · next t h => exact ((hI c t h).instL.liftN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [VExpr.liftN, expr, ihf, iha]
  | proj _ _ e ih => simp [VExpr.liftN, expr, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [VExpr.liftN, expr, ihA, ihb]

theorem expr_lift (hI : I.Closed) (e : VExpr) : I.expr e.lift = (I.expr e).lift :=
  expr_liftN hI e 1 0

theorem expr_inst (hI : I.Closed) (e a : VExpr) (k : Nat) :
    I.expr (e.inst a k) = (I.expr e).inst (I.expr a) k := by
  induction e generalizing k with
  | sort => rfl
  | bvar i =>
    simp only [VExpr.inst, VExpr.instVar, expr]
    split
    · rfl
    · split
      · exact expr_liftN hI a k 0
      · rfl
  | const c ls =>
    simp only [VExpr.inst, expr]
    split
    · next t h => exact ((hI c t h).instL.instN_eq (Nat.zero_le _)).symm
    · rfl
  | app f a ihf iha => simp [VExpr.inst, expr, ihf, iha]
  | proj _ _ e ih => simp [VExpr.inst, expr, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [VExpr.inst, expr, ihA, ihb]

theorem expr_instL (e : VExpr) (ls : List VLevel) :
    I.expr (e.instL ls) = (I.expr e).instL ls := by
  induction e with
  | bvar | sort => rfl
  | const c us =>
    simp only [VExpr.instL, expr]
    split
    · exact VExpr.instL_instL.symm
    · rfl
  | app f a ihf iha => simp [VExpr.instL, expr, ihf, iha]
  | proj _ _ e ih => simp [VExpr.instL, expr, ih]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [VExpr.instL, expr, ihA, ihb]

theorem instL_ne_forallE {t : VExpr} (h : ∀ A B, t ≠ VExpr.forallE A B) (ls : List VLevel) :
    ∀ A B, t.instL ls ≠ .forallE A B := by
  cases t <;> simp [VExpr.instL]
  exact h _ _ rfl

end VEnv.Interpretation

theorem Lookup.interpret {I : VEnv.Interpretation} (hI : I.Closed) (H : Lookup Γ i A) :
    Lookup (Γ.map I.expr) i (I.expr A) := by
  induction H with
  | zero => rw [VEnv.Interpretation.expr_lift hI]; exact .zero
  | succ _ ih => rw [VEnv.Interpretation.expr_lift hI]; exact .succ ih

/-! ### Patterns fixed by an interpretation

A pattern whose constants the interpretation fixes matches the interpretation of a term
exactly as it matches the term; a reduct whose fixed closed terms the interpretation fixes
commutes with the interpretation of the holes. These are the commutations behind
`PatClause.of_fixed`. -/

namespace Pattern

open VEnv.Interpretation

/-- Every constant of the pattern is kept by `I` (not interpreted, not renamed). -/
def ConstsFixed (I : VEnv.Interpretation) : Pattern → Prop
  | .const c => I.consts c = none ∧ I.rename c = c
  | .app f a => f.ConstsFixed I ∧ a.ConstsFixed I
  | .var f => f.ConstsFixed I

/-- Every fixed term of the reduct is kept by `I`. -/
def RHS.FixedTermsFixed (I : VEnv.Interpretation) {p : Pattern} : p.RHS → Prop
  | .fixed c _ => I.expr c = c
  | .app f a => f.FixedTermsFixed I ∧ a.FixedTermsFixed I
  | .var _ => True

/-- Every fixed term of the side conditions is kept by `I`. -/
def Check.FixedTermsFixed (I : VEnv.Interpretation) {p : Pattern} : p.Check → Prop
  | .true => True
  | .defeq a b rest => a.FixedTermsFixed I ∧ b.FixedTermsFixed I ∧ rest.FixedTermsFixed I

theorem Matches.interpret {I : VEnv.Interpretation} {p : Pattern} {e : VExpr} {m1 : List VLevel}
    {m2 : p.Path → VExpr} (hp : p.ConstsFixed I) (H : p.Matches e m1 m2) :
    p.Matches (I.expr e) m1 (fun x => I.expr (m2 x)) := by
  induction H with
  | const =>
    simp only [ConstsFixed] at hp
    rw [expr_const_none hp.1, hp.2]
    refine (congrArg (Pattern.Matches _ _ _) ?_).mpr .const
    funext x; exact nomatch x
  | @var f f' f1 g1 a' h ih =>
    simp only [ConstsFixed] at hp
    have ih := ih hp
    simp only [expr]
    refine (congrArg (Pattern.Matches _ _ _) ?_).mpr (.var ih)
    funext x; cases x <;> rfl
  | @app f f' f1 g1 a a' f2 g2 h1 h2 ih1 ih2 =>
    simp only [ConstsFixed] at hp
    have ih1 := ih1 hp.1
    have ih2 := ih2 hp.2
    simp only [expr]
    refine (congrArg (Pattern.Matches _ _ _) ?_).mpr (.app ih1 ih2)
    funext x; cases x <;> rfl

theorem RHS.apply_interpret {I : VEnv.Interpretation} {p : Pattern} {m1 : List VLevel}
    {m2 : p.Path → VExpr} : ∀ {r : p.RHS}, r.FixedTermsFixed I →
      I.expr (r.apply m1 m2) = r.apply m1 (fun x => I.expr (m2 x))
  | .fixed c _, h => by
    simp only [RHS.apply, expr_instL]
    rw [show I.expr c = c from h]
  | .var _, _ => rfl
  | .app f a, h => by
    simp only [RHS.apply, expr, RHS.apply_interpret h.1, RHS.apply_interpret h.2]

theorem Check.Realizes.interpret {I : VEnv.Interpretation} {p : Pattern} {m1 : List VLevel}
    {m2 : p.Path → VExpr} : ∀ {ck : p.Check} {chk : List (VExpr × VExpr × VExpr)},
      ck.FixedTermsFixed I → ck.Realizes m1 m2 chk →
      ck.Realizes m1 (fun x => I.expr (m2 x))
        (chk.map fun t => (I.expr t.1, I.expr t.2.1, I.expr t.2.2))
  | .true, [], _, _ => trivial
  | .true, _ :: _, _, h => h.elim
  | .defeq _ _ _, [], _, h => h.elim
  | .defeq a b rest, t :: ts, hck, ⟨h1, h2, h3⟩ => by
    refine ⟨?_, ?_, Check.Realizes.interpret hck.2.2 h3⟩
    · simp only [List.map_cons]; rw [h1, RHS.apply_interpret hck.1]
    · simp only [List.map_cons]; rw [h2, RHS.apply_interpret hck.2.1]

end Pattern

/-! ### Projection field types -/

namespace VProjectionInfo

open VEnv.Interpretation

theorem instantiateProjectionParameters_of_ne_forallE {x : VExpr}
    (h : ∀ A B, x ≠ .forallE A B) : instantiateProjectionParameters x (p :: ps) = none := by
  cases x <;> simp_all [instantiateProjectionParameters]

theorem instantiateProjectionFields_of_ne_forallE {x : VExpr}
    (h : ∀ A B, x ≠ .forallE A B) :
    instantiateProjectionFields typeName major wanted current fuel x = none := by
  cases fuel <;> cases x <;> simp_all [instantiateProjectionFields]

variable {I : VEnv.Interpretation}

theorem instantiateProjectionParameters_interpret (hI : I.Closed)
    (hT : I.PreservesTelescopes) (type : VExpr) (params : List VExpr) :
    instantiateProjectionParameters (I.expr type) (params.map I.expr) =
      (instantiateProjectionParameters type params).map I.expr := by
  induction params generalizing type with
  | nil => simp [instantiateProjectionParameters]
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters, expr]
    case const c ls =>
      cases h : I.consts c with
      | none => simp [instantiateProjectionParameters]
      | some t =>
        exact instantiateProjectionParameters_of_ne_forallE (instL_ne_forallE (hT c t h) ls)
    case forallE domain body =>
      rw [← expr_inst hI]
      exact ih (body.inst param)

theorem instantiateProjectionFields_interpret (hI : I.Closed) (hT : I.PreservesTelescopes)
    (type : VExpr) :
    instantiateProjectionFields (I.projOwner typeName) (I.expr major) wanted current fuel
        (I.expr type) =
      (instantiateProjectionFields typeName major wanted current fuel type).map I.expr := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, expr]
    case const c ls =>
      cases h : I.consts c with
      | none => simp [instantiateProjectionFields]
      | some t =>
        exact instantiateProjectionFields_of_ne_forallE (instL_ne_forallE (hT c t h) ls)
    case forallE domain body =>
      split
      · simp
      · change instantiateProjectionFields (I.projOwner typeName) (I.expr major) wanted
            (current + 1) fuel
            ((I.expr body).inst (.proj (I.projOwner typeName) current (I.expr major))) = _
        have : VExpr.proj (I.projOwner typeName) current (I.expr major) =
            I.expr (.proj typeName current major) := rfl
        rw [this, ← expr_inst hI]
        exact ih (current := current + 1) (body.inst (.proj typeName current major))

/-- Field types commute with interpretation of the constructor type, the parameters, the major
premise and the projection owner. -/
theorem fieldType_interpret (hI : I.Closed) (hT : I.PreservesTelescopes)
    (info : VProjectionInfo) :
    { info with ctorType := I.expr info.ctorType }.fieldType (I.projOwner typeName) levels
        (params.map I.expr) index (I.expr major) =
      (info.fieldType typeName levels params index major).map I.expr := by
  simp only [fieldType, List.length_map]
  split
  · rfl
  · rw [← expr_instL, instantiateProjectionParameters_interpret hI hT]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_interpret hI hT]

/-- `fieldType_interpret` when the interpretation fixes the constructor type and the owner. -/
theorem fieldType_interpret_of_fixed (hI : I.Closed) (hT : I.PreservesTelescopes)
    (info : VProjectionInfo) (hctor : I.expr info.ctorType = info.ctorType)
    (hown : I.projOwner typeName = typeName) :
    info.fieldType typeName levels (params.map I.expr) index (I.expr major) =
      (info.fieldType typeName levels params index major).map I.expr := by
  have h := fieldType_interpret (typeName := typeName) (levels := levels) (params := params)
    (index := index) (major := major) hI hT info
  rw [hctor, hown] at h
  exact h

end VProjectionInfo

/-! ### Context invariants -/

namespace VEnv

/-- A predicate on the contexts of `env`, closed under the context extensions made by the
typing rules: by a type (the binder rules) and by the type of a term (beta). -/
structure CtxInvariant (env : VEnv) (P : Nat → List VExpr → Prop) : Prop where
  type : ∀ {U Γ A u}, P U Γ → env.HasType U Γ A (.sort u) → P U (A :: Γ)
  inhabited : ∀ {U Γ e A}, P U Γ → env.HasType U Γ e A → P U (A :: Γ)

/-- Well-formed contexts. -/
abbrev TypedCtx (env : VEnv) (U : Nat) (Γ : List VExpr) : Prop := OnCtx Γ (env.IsType U)

theorem CtxInvariant.any {env : VEnv} : env.CtxInvariant fun _ _ => True :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

theorem CtxInvariant.typed {env : VEnv} (henv : env.Ordered) : env.CtxInvariant env.TypedCtx :=
  ⟨fun hΓ h => ⟨hΓ, _, h⟩, fun hΓ h => ⟨hΓ, h.isType henv hΓ⟩⟩

end VEnv

/-! ### Obligations -/

namespace VEnv.Interpretation

section Clauses

variable (I : Interpretation) (envS : VEnv) (P : Nat → List VExpr → Prop)

/-- The obligation for a constant `c : ci` of the source environment: an interpreting term has
the interpreted type; a renamed constant is a constant of `envS` whose type is definitionally
equal to the interpreted type. -/
def ConstClause (c : Name) (ci : VConstant) : Prop :=
  (∀ t, I.consts c = some t → envS.HasType ci.uvars [] t (I.expr ci.type)) ∧
  (I.consts c = none → ∃ ci', envS.constants (I.rename c) = some ci' ∧ ci'.uvars = ci.uvars ∧
    ∃ u, envS.IsDefEq ci.uvars [] ci'.type (I.expr ci.type) (.sort u))

/-- The obligation for a definitional axiom: its interpretation holds in `envS` at every
admissible universe instantiation. -/
def DefEqClause (df : VDefEq) : Prop :=
  ∀ {U : Nat} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    envS.IsDefEq U [] (I.expr (df.lhs.instL ls)) (I.expr (df.rhs.instL ls))
      (I.expr (df.type.instL ls))

/-- The obligation for a registered reduction rule `(p, r)` of the source environment: the
conclusion of `IsDefEq.pat` holds after interpretation, in every target context satisfying
`P`, once the interpreted premises do (the interpreted redex typed, the interpreted side
conditions derivable). The match itself is a premise on the uninterpreted redex: the
interpretation of a redex need not be a redex of a rule of `envS` (restoration interprets an
auxiliary constructor by a λ-abstraction, so the interpreted major is a β-redex), which is
why the clause may need the context invariant. -/
def PatClause (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {e A : VExpr} {m1 : List VLevel} {m2 : p.Path → VExpr}
    {chk : List (VExpr × VExpr × VExpr)},
    P U Γ → p.Matches e m1 m2 → envS.HasType U Γ (I.expr e) (I.expr A) →
    r.2.Realizes m1 m2 chk →
    (∀ t ∈ chk, envS.IsDefEq U Γ (I.expr t.1) (I.expr t.2.1) (I.expr t.2.2)) →
    envS.IsDefEq U Γ (I.expr e) (I.expr (r.1.apply m1 m2)) (I.expr A)

/-- The obligation for a projection `(typeName, info)` of the source environment: the
conclusions of its four rules hold after interpretation, in every target context satisfying
`P`, once the interpreted premises do. -/
structure ProjectionClause (typeName : Name) (info : VProjectionInfo) : Prop where
  projDF : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {index : Nat} {sourceMajor fieldType : VExpr} {fieldLevel : VLevel}
      {major : VExpr} {indexArgs : List VExpr} {major' : VExpr},
    P U Γ →
    (∀ l ∈ levels, l.WF U) → levels.length = info.uvars →
    params.length = info.nparams → indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    info.ctorType.Closed →
    ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) →
    envS.HasType U Γ (I.expr fieldType) (.sort fieldLevel) →
    envS.IsDefEq U Γ (I.expr sourceMajor) (I.expr major)
      (I.expr (VExpr.mkApps (.const typeName levels) (params ++ indexArgs))) →
    envS.IsDefEq U Γ (I.expr sourceMajor) (I.expr major')
      (I.expr (VExpr.mkApps (.const typeName levels) (params ++ indexArgs))) →
    envS.IsDefEq U Γ (I.expr (.proj typeName index major))
      (I.expr (.proj typeName index major')) (I.expr fieldType)
  projIota : ∀ {U : Nat} {Γ : List VExpr} {index : Nat} {levels : List VLevel}
      {args : List VExpr} {field fieldType : VExpr},
    P U Γ →
    envS.HasType U Γ
      (I.expr (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)))
      (I.expr fieldType) →
    args[info.nparams + index]? = some field →
    envS.HasType U Γ (I.expr field) (I.expr fieldType) →
    envS.IsDefEq U Γ
      (I.expr (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)))
      (I.expr field) (I.expr fieldType)
  structEta : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e : VExpr},
    P U Γ →
    params.length = info.nparams → info.nindices = 0 →
    envS.HasType U Γ (I.expr e) (I.expr (VExpr.mkApps (.const typeName levels) params)) →
    envS.HasType U Γ
      (I.expr (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e)))
      (I.expr (VExpr.mkApps (.const typeName levels) params)) →
    envS.IsDefEq U Γ
      (I.expr (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e)))
      (I.expr e) (I.expr (VExpr.mkApps (.const typeName levels) params))
  unitLike : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e e' : VExpr},
    P U Γ →
    params.length = info.nparams → info.nindices = 0 → info.numFields = 0 →
    envS.HasType U Γ (I.expr e) (I.expr (VExpr.mkApps (.const typeName levels) params)) →
    envS.HasType U Γ (I.expr e') (I.expr (VExpr.mkApps (.const typeName levels) params)) →
    envS.IsDefEq U Γ (I.expr e) (I.expr e')
      (I.expr (VExpr.mkApps (.const typeName levels) params))

end Clauses

/-- **The obligations of an interpretation** of `envL` in `envS`, for the context invariant
`P`. -/
structure Sound (I : Interpretation) (envS envL : VEnv) (P : Nat → List VExpr → Prop) :
    Prop where
  closed : I.Closed
  ordered : envS.OrderedStrong
  constants : ∀ c ci, envL.constants c = some ci → I.ConstClause envS c ci
  defeqs : ∀ df, envL.defeqs df → I.DefEqClause envS df
  pats : ∀ p r, envL.pats p r → I.PatClause envS P p r
  projections : ∀ typeName info, envL.projections typeName info →
    I.ProjectionClause envS P typeName info

variable {I : Interpretation} {envS : VEnv} {P : Nat → List VExpr → Prop}

/-! ### The transport theorem -/

/-- **Transport.** A sound interpretation maps every derivation of the source environment whose
interpreted context satisfies the context invariant to a derivation of the target
environment. -/
theorem Sound.isDefEq {envL : VEnv} (S : I.Sound envS envL P) (hP : envS.CtxInvariant P)
    {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : envL.IsDefEq U Γ e₁ e₂ A)
    (hΓ : P U (Γ.map I.expr)) :
    envS.IsDefEq U (Γ.map I.expr) (I.expr e₁) (I.expr e₂) (I.expr A) := by
  have hI := S.closed
  have henv := S.ordered
  revert hΓ
  induction H with
  | bvar h => intro _; exact .bvar (h.interpret hI)
  | symm _ ih => intro hΓ; exact .symm (ih hΓ)
  | trans _ _ ih1 ih2 => intro hΓ; exact .trans (ih1 hΓ) (ih2 hΓ)
  | sortDF h1 h2 h3 => intro _; exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' Γ₀ h1 h2 h3 h4 h5 =>
    intro _
    rw [expr_instL]
    obtain ⟨hrep, hkept⟩ := S.constants c ci h1
    cases hc : I.consts c with
    | some t =>
      rw [expr_const_some hc, expr_const_some hc]
      exact (IsDefEq.instL_r henv (Γ := []) trivial h2 h3 h5 (hrep t hc)).weak0 henv.ordered
    | none =>
      rw [expr_const_none hc, expr_const_none hc]
      obtain ⟨ci', hci', hu, _, ht⟩ := hkept hc
      exact .defeqDF ((ht.instL h2 (Γ := [])).weak0 henv.ordered)
        (.constDF hci' h2 h3 (h4.trans hu.symm) h5)
  | appDF _ _ ih1 ih2 =>
    intro hΓ
    rw [expr_inst hI]
    exact .appDF (ih1 hΓ) (ih2 hΓ)
  | projDF hinfo hlevels huvars hparams hindices hfield _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    intro hΓ
    exact (S.projections _ _ hinfo).projDF hΓ hlevels huvars hparams hindices hfield hclosed
      hguard (ihField hΓ) (ihLeft hΓ) (ihRight hΓ)
  | lamDF _ _ ih1 ih2 =>
    intro hΓ
    have ih1 := ih1 hΓ
    exact .lamDF ih1 (ih2 (hP.type hΓ ih1.hasType.1))
  | forallEDF _ _ ih1 ih2 =>
    intro hΓ
    have ih1 := ih1 hΓ
    exact .forallEDF ih1 (ih2 (hP.type hΓ ih1.hasType.1))
  | defeqDF _ _ ih1 ih2 => intro hΓ; exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    intro hΓ
    have ih2 := ih2 hΓ
    have ih1 := ih1 (hP.inhabited hΓ ih2)
    simp only [expr, expr_inst hI]
    exact .beta ih1 ih2
  | eta _ ih =>
    intro hΓ
    simp only [expr, expr_lift hI]
    exact .eta (ih hΓ)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro hΓ; exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 h3 => intro _; exact (S.defeqs _ h1 h2 h3).weak0 henv.ordered
  | pat hp hm _ hreal _ ihe ihchk =>
    intro hΓ
    exact (S.pats _ _ hp) hΓ hm (ihe hΓ) hreal fun t ht => ihchk t ht hΓ
  | projIota h1 _ h3 _ ih1 ih2 =>
    intro hΓ
    exact (S.projections _ _ h1).projIota hΓ (ih1 hΓ) h3 (ih2 hΓ)
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    intro hΓ
    exact (S.projections _ _ h1).structEta hΓ h2 h3 (ih1 hΓ) (ih2 hΓ)
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    intro hΓ
    exact (S.projections _ _ h1).unitLike hΓ h2 h3 h4 (ih1 hΓ) (ih2 hΓ)

theorem Sound.hasType {envL : VEnv} (S : I.Sound envS envL P) (hP : envS.CtxInvariant P)
    {U : Nat} {Γ : List VExpr} {e A : VExpr} (H : envL.HasType U Γ e A)
    (hΓ : P U (Γ.map I.expr)) :
    envS.HasType U (Γ.map I.expr) (I.expr e) (I.expr A) :=
  S.isDefEq hP H hΓ

/-- Transport of definitionally equal contexts over a base whose interpretation satisfies the
invariant; the interpreted contexts satisfy it as well. -/
theorem Sound.isDefEqCtx {envL : VEnv} (S : I.Sound envS envL P) (hP : envS.CtxInvariant P)
    {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr} (H : envL.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (hΓ₀ : P U (Γ₀.map I.expr)) :
    envS.IsDefEqCtx U (Γ₀.map I.expr) (Γ₁.map I.expr) (Γ₂.map I.expr) ∧
      P U (Γ₁.map I.expr) := by
  induction H with
  | zero => exact ⟨.zero, hΓ₀⟩
  | succ _ hA ih =>
    obtain ⟨ih, hΓ₁⟩ := ih
    have hA := S.isDefEq hP hA hΓ₁
    exact ⟨.succ ih hA, hP.type hΓ₁ hA.hasType.1⟩

/-! ### Weakening the invariant -/

theorem PatClause.weaken {Q : Nat → List VExpr → Prop} {p : Pattern} {r : p.RHS × p.Check}
    (H : I.PatClause envS P p r) (h : ∀ {U Γ}, Q U Γ → P U Γ) : I.PatClause envS Q p r :=
  fun hΓ => H (h hΓ)

theorem ProjectionClause.weaken {Q : Nat → List VExpr → Prop} {typeName : Name}
    {info : VProjectionInfo} (H : I.ProjectionClause envS P typeName info)
    (h : ∀ {U Γ}, Q U Γ → P U Γ) : I.ProjectionClause envS Q typeName info where
  projDF hΓ := H.projDF (h hΓ)
  projIota hΓ := H.projIota (h hΓ)
  structEta hΓ := H.structEta (h hΓ)
  unitLike hΓ := H.unitLike (h hΓ)

/-- A sound interpretation for an invariant is sound for every stronger invariant. -/
theorem Sound.weaken {Q : Nat → List VExpr → Prop} {envL : VEnv} (S : I.Sound envS envL P)
    (h : ∀ {U Γ}, Q U Γ → P U Γ) : I.Sound envS envL Q where
  closed := S.closed
  ordered := S.ordered
  constants := S.constants
  defeqs := S.defeqs
  pats p r hp := PatClause.weaken (S.pats p r hp) h
  projections typeName info hp := (S.projections typeName info hp).weaken h

/-! ### Clauses for pieces fixed by the interpretation -/

/-- A definitional axiom of `envS` with the interpreted sides discharges the clause of an
axiom. -/
theorem DefEqClause.of_rule {df df' : VDefEq} (hS : envS.defeqs df')
    (hu : df'.uvars = df.uvars) (hl : df'.lhs = I.expr df.lhs) (hr : df'.rhs = I.expr df.rhs)
    (ht : df'.type = I.expr df.type) : I.DefEqClause envS df := by
  intro U ls h2 h3
  simp only [expr_instL, ← hl, ← hr, ← ht]
  exact .extra hS h2 (h3.trans hu.symm)

/-- A reduction rule registered in `envS` whose constants and fixed reduct terms the
interpretation fixes discharges its own clause, in every context: the interpretation of a
redex is a redex of the same rule (`Pattern.Matches.interpret`), with the interpreted holes. -/
theorem PatClause.of_fixed {p : Pattern} {r : p.RHS × p.Check} (hS : envS.pats p r)
    (hp : p.ConstsFixed I) (hr : r.1.FixedTermsFixed I) (hc : r.2.FixedTermsFixed I) :
    I.PatClause envS P p r := by
  intro U Γ e A m1 m2 chk _ hm hty hreal hchk
  rw [Pattern.RHS.apply_interpret hr]
  refine .pat hS (hm.interpret hp) hty (hreal.interpret hc) fun t ht => ?_
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact hchk t' ht'

/-- A projection registered in `envS` with the same data, whose owner, constructor and
constructor type the interpretation fixes. -/
theorem ProjectionClause.of_fixed {typeName : Name} {info : VProjectionInfo}
    (hI : I.Closed) (hT : I.PreservesTelescopes) (hS : envS.projections typeName info)
    (htn : I.consts typeName = none) (hrtn : I.rename typeName = typeName)
    (hptn : I.projOwner typeName = typeName) (hctorName : I.consts info.ctorName = none)
    (hrctor : I.rename info.ctorName = info.ctorName)
    (hctor : I.expr info.ctorType = info.ctorType) :
    I.ProjectionClause envS P typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      _ hlevels huvars hparams hindices hfield hclosed hguard ihField ihLeft ihRight
    have hfield' := VProjectionInfo.fieldType_interpret_of_fixed (levels := levels)
      (params := params) (index := index) (major := sourceMajor) hI hT info hctor hptn
    rw [hfield] at hfield'
    simp only [expr_mkApps, List.map_append, expr_const_none htn, hrtn] at ihLeft ihRight
    simp only [expr, hptn]
    exact .projDF hS hlevels huvars (by simpa using hparams) (by simpa using hindices)
      hfield' ihField ihLeft ihRight hclosed hguard
  projIota := by
    intro U Γ index levels args field fieldType _ ih1 h3 ih2
    simp only [expr, expr_mkApps, hctorName, hrctor, hptn] at ih1 ⊢
    exact .projIota hS ih1 (by simp [h3]) ih2
  structEta := by
    intro U Γ levels params e _ h2 h3 ih1 ih2
    simp only [expr, expr_mkApps, List.map_append, List.map_map, Function.comp_def, hctorName,
      htn, hrctor, hrtn, hptn] at ih1 ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  unitLike := by
    intro U Γ levels params e e' _ h2 h3 h4 ih1 ih2
    simp only [expr_mkApps, expr_const_none htn, hrtn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 h4 ih1 ih2

/-! ### Building a sound interpretation along an installation -/

/-- A base environment, contained in `envS`, every piece of which the interpretation fixes. -/
theorem Sound.of_le {base : VEnv} (hI : I.Closed) (hT : I.PreservesTelescopes)
    (hS : envS.OrderedStrong) (hbase : base.Ordered) (hle : base ≤ envS)
    (hconst : ∀ c ci, base.constants c = some ci →
      I.consts c = none ∧ I.rename c = c ∧ I.projOwner c = c ∧ I.expr ci.type = ci.type)
    (hdefeqs : ∀ df, base.defeqs df →
      I.expr df.lhs = df.lhs ∧ I.expr df.rhs = df.rhs ∧ I.expr df.type = df.type)
    (hpats : ∀ p r, base.pats p r →
      p.ConstsFixed I ∧ r.1.FixedTermsFixed I ∧ r.2.FixedTermsFixed I) :
    I.Sound envS base P where
  closed := hI
  ordered := hS
  constants c ci hc := by
    obtain ⟨hn, hr, -, hty⟩ := hconst c ci hc
    refine ⟨fun t ht => (by rw [hn] at ht; cases ht), fun _ => ?_⟩
    obtain ⟨u, hu⟩ := hbase.constWF hc
    refine ⟨ci, by rw [hr]; exact hle.constants hc, rfl, u, ?_⟩
    rw [hty]
    exact hu.mono hle
  defeqs df hdf := by
    obtain ⟨hl, hr, ht⟩ := hdefeqs df hdf
    exact DefEqClause.of_rule (hle.defeqs hdf) rfl hl.symm hr.symm ht.symm
  pats p r hp :=
    let ⟨h1, h2, h3⟩ := hpats p r hp
    PatClause.of_fixed (hle.pats hp) h1 h2 h3
  projections typeName info hp := by
    obtain ⟨ci, htn⟩ := hbase.projectionConstant hp
    have hctor := hbase.projectionConstructor hp
    obtain ⟨h1, h2, h3, _⟩ := hconst _ _ htn
    obtain ⟨h4, h5, _, h6⟩ := hconst _ _ hctor
    exact ProjectionClause.of_fixed hI hT (hle.projections hp) h1 h2 h3 h4 h5 h6

/-- Extend a sound interpretation by one constant. -/
theorem Sound.addConst {env env' : VEnv} {n : Name} {ci : VConstant} (S : I.Sound envS env P)
    (h : env.addConst n ci = some env') (hc : I.ConstClause envS n ci) :
    I.Sound envS env' P where
  closed := S.closed
  ordered := S.ordered
  constants c ci' hc' := by
    by_cases hn : n = c
    · subst hn
      rw [VEnv.addConst_self h] at hc'
      cases hc'
      exact hc
    · rw [VEnv.addConst_constants_of_ne h hn] at hc'
      exact S.constants c ci' hc'
  defeqs df hdf := S.defeqs df (by rwa [VEnv.addConst_defeqs h] at hdf)
  pats p r hp := S.pats p r (by rwa [VEnv.addConst_pats h] at hp)
  projections typeName info hp :=
    S.projections typeName info (by rwa [VEnv.addConst_projections h] at hp)

/-- Extend a sound interpretation by a list of constants. -/
theorem Sound.addConstVals {env env' : VEnv} :
    ∀ {cs : List VConstVal}, I.Sound envS env P → env.addConstVals cs = some env' →
      (∀ c ∈ cs, I.ConstClause envS c.name c.toVConstant) → I.Sound envS env' P
  | [], S, h, _ => by cases h; exact S
  | c :: cs, S, h, hc => by
    simp only [VEnv.addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h₁, h₂⟩ := h
    exact Sound.addConstVals (S.addConst h₁ (hc c List.mem_cons_self)) h₂
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

/-- Extend a sound interpretation by projections. -/
theorem Sound.addProjections {env : VEnv} (S : I.Sound envS env P)
    {entries : List VProjectionEntry}
    (hp : ∀ entry ∈ entries, I.ProjectionClause envS P entry.typeName entry.info) :
    I.Sound envS (env.addProjections entries) P where
  closed := S.closed
  ordered := S.ordered
  constants c ci hc := S.constants c ci (by rwa [VEnv.addProjections_constants] at hc)
  defeqs df hdf := S.defeqs df (by rwa [VEnv.addProjections_defeqs] at hdf)
  pats p r hp := S.pats p r (by rwa [VEnv.addProjections_pats] at hp)
  projections typeName info h := by
    rcases VEnv.addProjections_iff.mp h with ⟨entry, hmem, rfl, rfl⟩ | h
    · exact hp entry hmem
    · exact S.projections typeName info h

/-- Extend a sound interpretation by one reduction rule. -/
theorem Sound.addPat {env : VEnv} (S : I.Sound envS env P) {p : Pattern} {r : p.RHS × p.Check}
    (hp : I.PatClause envS P p r) : I.Sound envS (env.addPat p r) P where
  closed := S.closed
  ordered := S.ordered
  constants := S.constants
  defeqs := S.defeqs
  pats p' r' h := by
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hp
    · exact S.pats p' r' h
  projections := S.projections

end VEnv.Interpretation
end Lean4Lean
