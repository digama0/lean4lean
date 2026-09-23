import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

/-!
# Inductive declarations

The shapes of recursor types, constructor types and ι-rule reducts (`VExpr.RecShape`,
`VExpr.CtorShape`, `VExpr.RuleShape`, with `VExpr.MotiveShape`/`VExpr.MinorFor` for the
motive and minor premises), the strict-positivity and result-type conditions on
constructors (`VExpr.CtorPositive`, `VExpr.CtorResult`), the large-elimination judgment
(`VInductDecl.LargeElim`), the staged environment extension `VEnv.addInduct` (type formers,
constructors, recursors, ι rules), and the declaration well-formedness predicate
`VInductDecl.WF` it is checked against.
-/

namespace VExpr

/-! ### Positivity and the result type of a constructor (thesis §2.6.1) -/

/-- One of the constants `cs` occurs in the expression. Mirrors the kernel's `hasIndOcc`
(`Inductive/Add.lean`), used there over the type formers of the block being declared. -/
def MentionsConst (cs : List Name) : VExpr → Prop
  | .bvar _ | .sort _ => False
  | .const c _ => c ∈ cs
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => MentionsConst cs e₁ ∨ MentionsConst cs e₂

/-- The boolean decision procedure behind `VExpr.MentionsConst`. -/
def mentionsConst (cs : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => decide (c ∈ cs)
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => mentionsConst cs e₁ || mentionsConst cs e₂

theorem mentionsConst_iff {cs : List Name} :
    ∀ {e : VExpr}, e.mentionsConst cs = true ↔ e.MentionsConst cs
  | .bvar _ | .sort _ | .const .. => by simp [mentionsConst, MentionsConst]
  | .app .. | .lam .. | .forallE .. => by
    simp [mentionsConst, MentionsConst, mentionsConst_iff]

/-- Thesis §2.6.1, the result type of a constructor of `T`: a Π-telescope of `np` parameters
and `nf` fields ending in `T` applied to the parameter variables in order and then `nind`
index terms. -/
def CtorResult (ty : VExpr) (T : Name) (np nf nind : Nat) : Prop :=
  ty.piArity = np + nf ∧
  ∃ us idx, idx.length = nind ∧ ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx)

theorem CtorResult_iff {ty : VExpr} {T : Name} {np nf nind : Nat} :
    ty.CtorResult T np nf nind ↔
      ty.piArity = np + nf ∧ ty.piBody.headConst? = some T ∧
        bvarsDesc nf np <+: ty.piBody.getAppArgs ∧
        (ty.piBody.getAppArgs.drop np).length = nind := by
  refine and_congr_right fun _ => ?_
  have : (∃ us idx, idx.length = nind ∧
      ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx)) ↔
      ∃ us idx, ty.piBody = (VExpr.const T us).mkApps (bvarsDesc nf np ++ idx) ∧
        idx.length = nind :=
    ⟨fun ⟨us, idx, h1, h2⟩ => ⟨us, idx, h2, h1⟩, fun ⟨us, idx, h1, h2⟩ => ⟨us, idx, h2, h1⟩⟩
  rw [this, eq_const_mkApps_append_iff (P := fun idx => idx.length = nind), bvarsDesc_length]

/-- Thesis §2.6.3, the major premise `z : P p x` of a recursor over `T`: `T` applied to the
recursor's own parameter variables and to its index variables. -/
def MajorApp (A : VExpr) (T : Name) (np nm nmin nind : Nat) : Prop :=
  ∃ us, A = (VExpr.const T us).mkApps (bvarsDesc (nm + nmin + nind) np ++ bvarsDesc 0 nind)

theorem MajorApp_iff {A : VExpr} {T : Name} {np nm nmin nind : Nat} :
    A.MajorApp T np nm nmin nind ↔
      A.headConst? = some T ∧
        A.getAppArgs = bvarsDesc (nm + nmin + nind) np ++ bvarsDesc 0 nind :=
  eq_const_mkApps_iff

/-- Thesis §2.6.1, the kernel's `isValidIndApp?`: an application of one of the block's type
formers `fs` to the block's parameter variables — seen from `d` binders below the field
level — and to index terms in which no former occurs. -/
def ValidIndApp (fs : List Name) (np d : Nat) (e : VExpr) : Prop :=
  ∃ T ∈ fs, ∃ us idx, e = (VExpr.const T us).mkApps (bvarsDesc d np ++ idx) ∧
    ∀ a ∈ idx, ¬ a.MentionsConst fs

theorem ValidIndApp_iff {fs : List Name} {np d : Nat} {e : VExpr} :
    e.ValidIndApp fs np d ↔
      (∃ T, e.headConst? = some T ∧ T ∈ fs) ∧ bvarsDesc d np <+: e.getAppArgs ∧
        ∀ a ∈ e.getAppArgs.drop np, ¬ a.MentionsConst fs := by
  simp only [ValidIndApp, eq_const_mkApps_append_iff, bvarsDesc_length]
  constructor
  · rintro ⟨T, hT, hc, hpre, hidx⟩; exact ⟨⟨T, hc, hT⟩, hpre, hidx⟩
  · rintro ⟨⟨T, hc, hT⟩, hpre, hidx⟩; exact ⟨T, hT, hc, hpre, hidx⟩

/-- Thesis §2.6.1, strict positivity of one constructor field, mirroring the kernel's
`checkPositivity`: either no former of `fs` occurs in the field type, or it is
`∀ x₁ … x_k, B` with no `xᵢ`'s type mentioning a former and `B` a `ValidIndApp`. The kernel
reduces the field type (and each `xᵢ`'s) to weak head normal form first; the model reads the
manifest binders only. -/
def FieldPositive (fs : List Name) (np d : Nat) (ty : VExpr) : Prop :=
  ¬ ty.MentionsConst fs ∨
    ((∀ A ∈ ty.piBinders, ¬ A.MentionsConst fs) ∧
      ty.piBody.ValidIndApp fs np (d + ty.piArity))

/-- Thesis §2.6.1, strict positivity of a constructor with `np` parameters: no former of
`fs` occurs in a parameter binder, and every later binder — field `i`, sitting under `np + i`
binders — is `FieldPositive`. The result type is pinned separately, by `CtorResult`. -/
def CtorPositive (fs : List Name) (np : Nat) (ty : VExpr) : Prop :=
  (∀ A ∈ ty.piBinders.take np, ¬ A.MentionsConst fs) ∧
  ∀ i < ty.piArity - np, ∃ A, ty.piBinders[np + i]? = some A ∧ A.FieldPositive fs np i

/-- Field `i` of a constructor with `np` parameters occurs among the index arguments of its
result type: the syntactic clause of the kernel's `isLargeEliminator`. -/
def FieldInIndices (ty : VExpr) (np i : Nat) : Prop :=
  VExpr.bvar (ty.piArity - np - 1 - i) ∈ ty.piBody.getAppArgs.drop np

/-- The de Bruijn context of field `i` of a constructor with `np` parameters: the parameter
and earlier-field binder types, innermost first. -/
def fieldCtx (ty : VExpr) (np i : Nat) : List VExpr := (ty.piBinders.take (np + i)).reverse

/-! ### Recursor, constructor and ι-reduct shapes (thesis §2.6.3–2.6.4) -/

/-- Thesis §2.6.3, the motive `C : ∀ a::α. P a → U`: a Π-telescope ending in a sort whose
last binder is headed by a constant (`VExpr.motiveFormer?`, that head). *Which* constant is
not pinned here — a bare `VEnv` has no notion of type former — and `RecShape` ties only the
eliminated motive's head to the major premise's; the heads of the other motives of a
mutual recursor are unconstrained. -/
def MotiveShape (A : VExpr) : Prop :=
  (∃ u, A.piBody = .sort u) ∧ A.motiveFormer?.isSome = true

/-- Thesis §2.6.3, the head `C` of the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)`:
the Π-body of minor `i` (counted from the outermost minor binder) is headed by one of the
`nm` motives. Under the minor's own `piArity` binders, the motive binders — which precede
minor `i` by `i` minors — are `bvar (piArity + i + k)` for `k < nm` (motive `nm - 1 - k`). -/
def MinorHeaded (A : VExpr) (i nm : Nat) : Prop :=
  ∃ k < nm, A.piBody.getAppFn = .bvar (A.piArity + i + k)

/-- Thesis §2.6.3, the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)` of constructor
`c`: a Π-telescope ending in an application of a bound variable (the motive, which
`RecShape` pins on the same binder) whose last argument is headed by `c`. -/
def MinorFor (A : VExpr) (c : Name) : Prop :=
  A.RecHeaded ∧ ∃ x, A.piBody.getAppArgs.getLast? = some x ∧ x.headConst? = some c

/-- Thesis §2.6.3: the recursor telescope is `∀ params motives minors indices major,
motive_j indices major`, with motive `j` counted from the outermost motive binder. Motive
binders have the shape `MotiveShape`, minor binders end in an application of one of the
motives (`MinorHeaded`), the major premise is the type former `T` applied to the parameter
and index variables (`MajorApp`), and `motive_j`'s last binder is headed by `T` too.
Parameter and index binders are unconstrained. -/
def RecShape (ty : VExpr) (np nm nmin nind : Nat) : Prop :=
  ty.piArity = np + nm + nmin + nind + 1 ∧
  (∀ i < nm, ∃ A, ty.piBinders[np + i]? = some A ∧ A.MotiveShape) ∧
  (∀ i < nmin, ∃ A, ty.piBinders[np + nm + i]? = some A ∧ A.MinorHeaded i nm) ∧
  ∃ j < nm,
    (∃ M, ty.piBinders[np + nm + nmin + nind]? = some M ∧
      ∃ T, M.headConst? = some T ∧ M.MajorApp T np nm nmin nind ∧
        ∃ A, ty.piBinders[np + j]? = some A ∧ A.motiveFormer? = some T) ∧
    ty.piBody =
      (VExpr.bvar (nind + nmin + 1 + (nm - 1 - j))).mkApps (VExpr.bvarsDesc 0 (nind + 1))

/-- The syntactic shape of a constructor type: exactly `arity` Π-binders ending in a constant
application (`CtorHeaded`). Which binders are parameters and whether the constant is a type
former, a bare `VEnv` cannot say. -/
def CtorShape (ty : VExpr) (arity : Nat) : Prop := ty.piArity = arity ∧ ty.CtorHeaded

/-- The type former a recursor type with major index `idx` eliminates: the head constant of
its major premise (the `idx`-th Π-binder). -/
def majorFormer? (ty : VExpr) (idx : Nat) : Option Name :=
  ty.piBinders[idx]?.bind VExpr.headConst?

/-- Thesis §2.6.4: the reduct of the ι rule using minor `j` (counted from the outermost
minor binder) is `λ params motives minors fields, minor_j fields v`, minor `j` applied
η-long to the fields and then to `nrec` further arguments `v` (`recArgs`). The terms `v` are
not pinned, syntactically or through typing: `VInductDecl.WF.rules_wf` types the reduct at
the redex's type, which forces only the *types* of `v` — those of the minor's binders after
the fields (`δ`, themselves unpinned by `MinorFor`) — not that they are the thesis's
recursive calls `rec … (u_i x)`. Their *number* is pinned: `VInductDecl.WF.rule_shape` sets
`nrec` to the number of the minor's binders after the fields (`v::δ` has the length of `δ`),
so the reduct applies the minor to exactly its binders — none beyond the fields for a
non-recursive constructor. -/
def RuleShape (rhs : VExpr) (np nm nmin nf nrec j : Nat) : Prop :=
  rhs.lamArity = np + nm + nmin + nf ∧
  ∃ recArgs : List VExpr, recArgs.length = nrec ∧
    rhs.lamBody = (VExpr.bvar (nf + (nmin - 1 - j))).mkApps (VExpr.bvarsDesc 0 nf ++ recArgs)

end VExpr

/-- A rule reduct is a λ-abstraction: its λ-arity counts at least the minor premises, of
which there is at least one (`j < nmin`). -/
theorem VExpr.RuleShape.lam {rhs : VExpr} {np nm nmin nf nrec j : Nat}
    (h : rhs.RuleShape np nm nmin nf nrec j) (hj : j < nmin) : ∃ A b, rhs = .lam A b := by
  have h1 := h.1
  cases rhs with
  | lam A b => exact ⟨A, b, rfl⟩
  | _ => simp [VExpr.lamArity] at h1; omega

/-- A recursor type is `RecHeaded`: its Π-body is a motive application. -/
theorem VExpr.RecShape.recHeaded {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) : ty.RecHeaded :=
  h.2.2.2.elim fun _ hj => ⟨_, by rw [hj.2.2, VExpr.getAppFn_mkApps]; rfl⟩

/-- A recursor type has at least one motive. -/
theorem VExpr.RecShape.one_le_numMotives {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) : 1 ≤ nm :=
  h.2.2.2.elim fun _ hj => Nat.lt_of_le_of_lt (Nat.zero_le _) hj.1

/-- The type former a `RecShape` recursor eliminates: the head constant of its major
premise, which `MajorApp` pins to an application of the parameter and index variables. -/
theorem VExpr.RecShape.majorFormer?_eq {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) :
    ∃ T M, ty.piBinders[np + nm + nmin + nind]? = some M ∧
      ty.majorFormer? (np + nm + nmin + nind) = some T ∧ M.MajorApp T np nm nmin nind :=
  h.2.2.2.elim fun _ hj => hj.2.1.elim fun M hM => hM.2.elim fun T hT =>
    ⟨T, M, hM.1, by rw [VExpr.majorFormer?, hM.1]; exact hT.1, hT.2.1⟩

/-- A constructor returning its own type former has that constant as its Π-body's head. -/
theorem VExpr.CtorResult.ctorHeaded {ty : VExpr} {T : Name} {np nf nind : Nat}
    (h : ty.CtorResult T np nf nind) : ty.CtorHeaded := by
  obtain ⟨-, us, idx, -, hb⟩ := h
  exact ⟨T, us, by rw [hb, VExpr.getAppFn_mkApps]; rfl⟩

/-- A constructor returning its own type former has `CtorShape` of arity `np + nf`. -/
theorem VExpr.CtorResult.ctorShape {ty : VExpr} {T : Name} {np nf nind : Nat}
    (h : ty.CtorResult T np nf nind) : ty.CtorShape (np + nf) := ⟨h.1, h.ctorHeaded⟩

/-! ### Large elimination (thesis §2.6.2) -/

/-- Thesis §2.6.2, the kernel's `isLargeEliminator`: the block may eliminate into an
arbitrary sort. Either its result sort `ℓ` is never `Prop`, or the block is a single type
former with no constructor, or a single type former with one constructor each of whose
fields is a proposition or occurs among the indices of the constructor's result type. `env`
is the environment in which the fields are typed, the one with the type formers declared. -/
def VInductDecl.LargeElim (env : VEnv) (decl : VInductDecl) (ℓ : VLevel) : Prop :=
  ℓ.IsNeverZero ∨
  (∃ t, decl.types = [t] ∧ t.ctors = []) ∨
  (∃ t c, decl.types = [t] ∧ t.ctors = [c] ∧
    ∀ i < c.type.piArity - decl.nparams, ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧
      (env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero) ∨
        c.type.FieldInIndices decl.nparams i))

/-- The syntactic half of `VInductDecl.LargeElim`, decidable: a block outside the never-`Prop`
case is a single type former with at most one constructor. Whether a field of that
constructor is a proposition is a typing judgment, not decided here. -/
def VInductDecl.LargeElimShape (decl : VInductDecl) : Prop :=
  decl.types.length = 1 ∧ ∀ t ∈ decl.types, t.ctors.length ≤ 1

/-- A block whose result sort can be `Prop` eliminates largely only in the shape
`LargeElimShape` allows. -/
theorem VInductDecl.LargeElim.shape {env : VEnv} {decl : VInductDecl} {ℓ : VLevel}
    (h : decl.LargeElim env ℓ) (hz : ¬ ℓ.IsNeverZero) : decl.LargeElimShape := by
  rcases h with h | ⟨t, ht, hc⟩ | ⟨t, c, ht, hc, -⟩
  · exact absurd h hz
  · refine ⟨by rw [ht]; rfl, fun t' ht' => ?_⟩
    rw [ht, List.mem_singleton] at ht'; subst ht'; simp [hc]
  · refine ⟨by rw [ht]; rfl, fun t' ht' => ?_⟩
    rw [ht, List.mem_singleton] at ht'; subst ht'; simp [hc]

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
re-groups this into four stages — all type formers, all constructors, all recursors, then
all ι rules — which yields the same resulting environment as the kernel's interleaving,
not its literal order. Each stage is
named so that `VInductDecl.WF` can type each kind of constant in the environment the kernel
checks it in. -/

/-- Stage 0: add the type formers as constants. -/
def VInductDecl.addTypes (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.types.foldlM (init := env) fun e t => e.addConst t.name t.toVConstVal.toVConstant

/-- Stage 1: add the constructors of every type former, in block order. -/
def VInductDecl.addCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.types.flatMap (·.ctors)).foldlM (init := env) fun e c => e.addConst c.name c.toVConstant

/-- Stage 2: add the recursors as constants. -/
def VInductDecl.addRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r => e.addConst r.name r.toVConstVal.toVConstant

/-- Stage 3: register every recursor rule as an ι rule. -/
def VInductDecl.addRules (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru

/-- Stages 0–1: the environment the recursors are checked in. -/
def VInductDecl.addTypesCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypes env >>= decl.addCtors

/-- Stages 0–2: the environment the ι rules are registered in. -/
def VInductDecl.addTypesCtorsRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypesCtors env >>= decl.addRecs

/-- The constants of the declaration as `(name, constant)` pairs, in stage order (type
formers, constructors, recursors): stages 0–2 are the `addConst` fold over this list
(`VInductDecl.addTypesCtorsRecs_eq`). -/
def VInductDecl.consts (decl : VInductDecl) : List (Name × VConstant) :=
  decl.types.map (fun t => (t.name, t.toVConstVal.toVConstant)) ++
  (decl.types.flatMap (·.ctors)).map (fun c => (c.name, c.toVConstant)) ++
  decl.recs.map (fun r => (r.name, r.toVConstVal.toVConstant))

/-- Extend `env` with the type formers, constructors, and recursors of `decl` (as
constants) and its ι-reduction rules (as `pats`), or `none` on a name clash or a
non-closed rule reduct. The chain of `VInductDecl.addTypes`, `addCtors`, `addRecs`,
`addRules`. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.addTypesCtorsRecs env >>= decl.addRules

/-- Well-formedness of a **direct** mutual inductive block (thesis §2.6.1–2.6.4), staged
like the kernel's checks: type formers typed in `env`, constructors after the type formers
are declared, recursors after the constructors, ι rules after the recursors. Direct means
every recursor eliminates one of the block's own type formers (`recs_over_block`) and every
rule fires on one of that former's constructors (`rules_ctor`); a nested inductive — whose
constructors mention the block inside another type former (`Tree.node : List Tree → Tree`)
and whose auxiliary recursors eliminate that former — is therefore not well-formed here.
The kernel compiles such a block to a direct one (`ElimNestedInductive`, `Inductive/Add.lean`)
before checking it, and modelling that pass is future work. Typing checks the constants'
types (`types_wf`, `ctors_wf`, `recs_wf`), the universe of every constructor field and the
propositionality clause of large elimination (`universes`), and the ι rules (`rules_wf`);
every other clause is syntactic.

**Not modelled**: K-like reduction as a reduction rule (`addRecRule` installs only §2.6.4's
constructor rule, and the recorded flag `k` is unused); structure η; the kernel's `whnf` on
a field type, where `CtorPositive` and `universes` read the manifest binders. -/
structure VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop where
  /-- Type formers are typed in `env`. -/
  types_wf : ∀ t ∈ decl.types, t.toVConstVal.toVConstant.WF env
  /-- Constructors are typed once the type formers are declared. -/
  ctors_wf : ∀ envT, decl.addTypes env = some envT →
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.toVConstant.WF envT
  /-- Recursors are typed once the constructors are declared. -/
  recs_wf : ∀ envC, decl.addTypesCtors env = some envC →
    ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF envC
  /-- Type formers share the declaration's universe parameters. -/
  types_uvars : ∀ t ∈ decl.types, t.uvars = decl.uvars
  /-- So do the constructors. -/
  ctors_uvars : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.uvars = decl.uvars
  /-- §2.6.1–2.6.2: one result sort `ℓ` for the whole block, above the universe of every
  constructor field (`imax(ℓ', ℓ) ≤ ℓ`), and large elimination whenever a recursor asks for
  the extra universe parameter. -/
  universes : ∀ envT, decl.addTypes env = some envT → ∃ ℓ,
    (∀ t ∈ decl.types, t.type.piBody = .sort ℓ ∧ decl.nparams ≤ t.type.piArity) ∧
    (∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ i < c.type.piArity - decl.nparams,
      ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧ ∃ u,
        envT.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort u) ∧
        VLevel.imax u ℓ ≤ ℓ) ∧
    ((∃ r ∈ decl.recs, r.uvars = decl.uvars + 1) → decl.LargeElim envT ℓ)
  /-- §2.6.3, κ: a recursor has the block's universe parameters, plus one extra — the
  first, `VLevel.param 0` — exactly when it eliminates into an arbitrary sort; every motive
  then ends in `Sort (param 0)`, and otherwise in `Prop`. -/
  recs_elim : ∀ r ∈ decl.recs, (r.uvars = decl.uvars ∨ r.uvars = decl.uvars + 1) ∧
    ∀ i < r.numMotives, ∃ A, r.type.piBinders[r.numParams + i]? = some A ∧
      A.piBody = .sort (if r.uvars = decl.uvars + 1 then .param 0 else .zero)
  /-- Every recursor records the declaration's parameter count. -/
  rec_params : ∀ r ∈ decl.recs, r.numParams = decl.nparams
  /-- A constructor's parameter binders are its type former's. -/
  ctors_params : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
    c.type.piBinders.take decl.nparams = t.type.piBinders.take decl.nparams
  /-- §2.6.1: a constructor returns its own type former applied to the parameter variables
  and to as many index terms as the former has indices. -/
  ctors_result : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
    ∃ nf, c.type.CtorResult t.name decl.nparams nf (t.type.piArity - decl.nparams)
  /-- §2.6.1: every constructor is strictly positive in the block's type formers. -/
  ctors_positive : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
    c.type.CtorPositive (decl.types.map (·.name)) decl.nparams
  /-- The block is direct: every recursor eliminates one of its own type formers. -/
  recs_over_block : ∀ r ∈ decl.recs,
    ∃ t ∈ decl.types, r.type.majorFormer? r.getMajorIdx = some t.name
  /-- §2.6.3: a recursor has one motive per type former, one minor per constructor of the
  block, and as many indices as the type former it eliminates. -/
  rec_counts : ∀ r ∈ decl.recs, r.numMotives = decl.types.length ∧
    r.numMinors = (decl.types.flatMap (·.ctors)).length ∧
    ∀ t ∈ decl.types, r.type.majorFormer? r.getMajorIdx = some t.name →
      r.numIndices = t.type.piArity - decl.nparams
  /-- §2.6.3: the recursor telescope split and the shapes of its motives, minors and
  major premise. -/
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- A recursor has at most one rule per constructor. -/
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  /-- §2.6.4: every rule fires on a constructor of the type former its recursor eliminates,
  with the declaration's parameter count and the rule's declared field count. -/
  rules_ctor : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ t ∈ decl.types,
    r.type.majorFormer? r.getMajorIdx = some t.name ∧ ∃ c ∈ t.ctors,
      ru.ctor = c.name ∧ ru.ctorParams = decl.nparams ∧
      c.type.CtorResult t.name decl.nparams ru.nfields (t.type.piArity - decl.nparams)
  /-- Every type former of the block is eliminated by a recursor of the block. -/
  types_have_rec : ∀ t ∈ decl.types, ∃ r ∈ decl.recs, r.type.majorFormer? r.getMajorIdx = some t.name
  /-- §2.6.3/§2.6.4, `ε` has the length of `K`: a recursor has a rule for each constructor
  of the type former it eliminates (exactly one, by `rules_nodup`). -/
  rules_total : ∀ r ∈ decl.recs, ∀ t ∈ decl.types, r.type.majorFormer? r.getMajorIdx = some t.name →
    ∀ c ∈ t.ctors, ∃ ru ∈ r.rules, ru.ctor = c.name
  /-- §2.6.4, the reduct shape, tied to §2.6.3's constructor↔minor correspondence: the rule
  for `ru.ctor` reduces to minor `j`, a minor whose last argument is headed by `ru.ctor`,
  applied to the `nfields` fields and to exactly as many further arguments as the minor has
  binders after the fields (thesis `e_c b v`, `v::δ`). A count only: the terms `v` are
  pinned by nothing here. -/
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  /-- §2.6.4 as a typing, the `VDefEq.WF` of an ι rule: as registered by `addRecRule`, in
  the stage-2 environment, the rule is typed (`VEnv.PatTyped`, the typing half of
  `VEnv.PatWF`; the other half, the template shape of the reduct, is `rule_shape`) — its
  generic redex `rec params motives minors idx (c cargs fields)` and reduct
  `rhs params motives minors fields` are typed at a common type in the context of the
  parameters, motives, minors and fields. No kernel check performs it: it is the model's
  admissibility condition for registering the rule, the analogue of the thesis's regularity
  of reductions for the generic rule. -/
  rules_wf : ∀ envR, decl.addTypesCtorsRecs env = some envR → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∀ hc : ru.rhs.Closed,
    envR.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

/-- Every constructor of the block has a rule in some recursor of the block
(`types_have_rec` and `rules_total`). -/
theorem VInductDecl.WF.ctors_have_rules {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∃ r ∈ decl.recs, ∃ ru ∈ r.rules, ru.ctor = c.name := by
  intro t ht c hc
  obtain ⟨r, hr, hmaj⟩ := H.types_have_rec t ht
  obtain ⟨ru, hru, hctor⟩ := H.rules_total r hr t ht hmaj c hc
  exact ⟨r, hr, ru, hru, hctor⟩

/-- Every rule records its recursor's parameter count: its constructor is one of the block's
own, so it has the declaration's parameters (`rules_ctor`), as does the recursor
(`rec_params`). -/
theorem VInductDecl.WF.rules_own_params {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.ctorParams = r.numParams := by
  intro r hr ru hru
  obtain ⟨-, -, -, -, -, -, hnp, -⟩ := H.rules_ctor r hr ru hru
  rw [hnp, H.rec_params r hr]
