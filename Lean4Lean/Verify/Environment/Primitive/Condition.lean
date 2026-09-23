import Lean4Lean.Verify.Environment.Primitive.Basic

/-!
`Condition`: a decidable predicate together with the evidence that its decision procedure decides
it, and the two conditional equations a recognizer builds out of one.
-/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-! ### Conditionals

A `Condition` packages a decidable predicate with the evidence that its decision procedure
agrees with `ite`; `Condition.check` verifies that evidence and `Condition.ite`/`dite`/`decide`
build conditionals out of it. `Condition.WF` below is the model-side reading of those checks --
one field per group of checks -- and is the whole of what a caller gets to use.

Two things are pulled out of the raw checks rather than transcribed.

*The context.* Everything is stated in the empty context. A `Condition` is a closed constant of
the checker (`natLE`, `natEq`, `bool`), so nothing it says depends on where the check runs, and
a ground fact weakens to any context with `weak0`. `Nat.mod` and `Nat.div` already call
`Condition.check` before their first `withLocalDecl`; the calls in `Nat.bitwise` and in
`unfoldNatWellFounded`'s `eager` gadget currently sit under binders, but neither mentions
anything local, so both can be hoisted. Without that hoisting these statements would have to
carry the check's context and a weakening along it, for no gain.

*The decision.* What varies between the three conditions is not the `ite` equations -- those
are the same shape -- but when the decision procedure is known to evaluate. That is `decides`,
a parameter here and a separate fact per condition: `bool` decides its own scrutinee, while
`natLE` and `natEq` decide by `asBool`, which their branches' guards make a reflected
primitive (`Nat.ble`, `Nat.beq`). Keeping it a parameter is what lets the two `ite`/`dite`
fields be shared by all three. -/

/-- `@ite.{1} α p inst t e`, the shape `Condition.ite` builds. -/
def iteApp (α p inst t e : VExpr) : VExpr :=
  (((((VExpr.const ``ite [.succ .zero]).app α).app p).app inst).app t).app e

/-- `@dite.{1} Nat p inst t e`, the shape `Condition.dite` builds. The branches are functions of
the decision -- `Nat.mod` and `Nat.div` really do use it, as the `1 ≤ y` argument to `go`. -/
def diteApp (p inst t e : VExpr) : VExpr :=
  (((((VExpr.const ``dite [.succ .zero]).app .nat).app p).app inst).app t).app e

/-- A `Reflection` together with its translation. `type'` and `toDec'` are carried rather than
existentially bound per fact because `WF_ite` and `WF_dite` are equations about both of them.
The one field beyond the translations is `Reflection.check`. -/
structure Reflection.WF (c : VContext) (r : Reflection) where
  type' : VExpr
  htype : c.TrExprS r.type type'
  /-- `Reflection.check`: the reflection is a relation between a proposition and a boolean. -/
  typeT : c.HasType type' vexpr(Prop → Bool → Prop)

/-- What is known about `toDec`'s type: applied to a proposition, a boolean and evidence relating
them, it is well typed.

*Applied*, because that is all anything checks. `Reflection.check` does not check `toDec`'s type
-- `toDec` is only ever *used*, inside `ite`/`natDITE`, and it is those uses, whose binders are a
`Prop`, a `Bool` and a `type p b`, that pin its argument types. A typing obtained at someone
else's binders does not reassemble into a pi type, and the codomain is pinned by nothing at all.

*Not a field of `Reflection.WF`*, because only the two optional checks establish it. It is what
`ITE_T`/`DITE_T` deliver on the side, and every consumer of it -- the two bridges below -- runs
under one of those flags anyway. -/
def Reflection.WF.ToDecT {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (toDec' : VExpr) : Prop :=
  ∀ (E : c.Ext) ⦃Γ : List VExpr⦄ {p bb H : VExpr}, OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p (.sort .zero) →
    E.venv.HasType c.lparams.length Γ bb .bool →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app bb) →
    VExpr.WF E.venv c.lparams.length Γ (((toDec'.app p).app bb).app H)

/-- The pi types of the three functions in `toDec`'s spine, each with the domain its argument was
given. Congruence in an argument needs exactly this, and `app_inv` is the whole proof: the
domains are not identified with `Prop`/`Bool`/`type p b` here because a consumer that has to
convert an argument does it against the type it has anyway. -/
theorem Reflection.WF.ToDecT.spine {c : VContext} {r : Reflection} {w : Reflection.WF c r}
    {toDec' : VExpr} (h : w.ToDecT toDec') (E : c.Ext) {Γ : List VExpr} {p bb H : VExpr}
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hp : E.venv.HasType c.lparams.length Γ p (.sort .zero))
    (hbb : E.venv.HasType c.lparams.length Γ bb .bool)
    (hH : E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app bb)) :
    ∃ A₁ B₁ A₂ B₂ A₃ B₃,
      (E.venv.HasType c.lparams.length Γ toDec' (.forallE A₁ B₁) ∧
        E.venv.HasType c.lparams.length Γ p A₁) ∧
      (E.venv.HasType c.lparams.length Γ (toDec'.app p) (.forallE A₂ B₂) ∧
        E.venv.HasType c.lparams.length Γ bb A₂) ∧
      (E.venv.HasType c.lparams.length Γ ((toDec'.app p).app bb) (.forallE A₃ B₃) ∧
        E.venv.HasType c.lparams.length Γ H A₃) := by
  obtain ⟨_, _, hf₃, ha₃⟩ := VExpr.WF.app_inv E.wf hΓ (h E hΓ hp hbb hH)
  obtain ⟨_, _, hf₂, ha₂⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf₃⟩
  obtain ⟨_, _, hf₁, ha₁⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf₂⟩
  exact ⟨_, _, _, _, _, _, ⟨hf₁, ha₁⟩, ⟨hf₂, ha₂⟩, ⟨hf₃, ha₃⟩⟩

/-- `Reflection.checkITE`: at reflection evidence for a boolean literal, `ite` on the decision
the reflection produces is the corresponding branch.

Quantified over the context, unlike the fields above. Those are about the reflection's own closed
pieces, which live at `[]` and weaken; this is about the *caller's* proposition, evidence and
branches, which live past whatever binders the caller has opened, and a `c`-level statement could
not be transported to them. The check itself is run under two `withLocalDecl`s at closed types,
so it holds at every context by weakening and instantiating those two binders. -/
def Reflection.WF.WF_ite (w : Reflection.WF c r) (toDec' : VExpr) : Prop :=
  ∀ (E : c.Ext) {Γ : List VExpr} {p H α t e : VExpr} (b : Bool),
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p (.sort .zero) →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app (.boolLit b)) →
    E.venv.HasType c.lparams.length Γ α (.sort (.succ .zero)) →
    E.venv.HasType c.lparams.length Γ t α → E.venv.HasType c.lparams.length Γ e α →
    E.venv.IsDefEqU c.lparams.length Γ
      (iteApp α p (((toDec'.app p).app (.boolLit b)).app H) t e) (if b then t else e)

/-- `Reflection.checkNatDITE`: likewise for `dite`, whose branches are applied to the proof
that `ofTrue`/`ofFalse` extract from the evidence. Those two are existential here rather than
fields of `Reflection.WF` because only this check types them. -/
def Reflection.WF.WF_dite (w : Reflection.WF c r) (toDec' : VExpr) : Prop :=
  ∃ ofTrue' ofFalse',
    c.TrExprS r.ofTrue ofTrue' ∧ c.TrExprS r.ofFalse ofFalse' ∧
    ∀ (E : c.Ext) {Γ : List VExpr} {p H t e : VExpr} (b : Bool),
      OnCtx Γ (E.venv.IsType c.lparams.length) →
      E.venv.HasType c.lparams.length Γ p (.sort .zero) →
      E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app (.boolLit b)) →
      E.venv.HasType c.lparams.length Γ t (.forallE p .nat) →
      E.venv.HasType c.lparams.length Γ e (.forallE (vexpr(Not).app p) .nat) →
      E.venv.IsDefEqU c.lparams.length Γ
        (diteApp p (((toDec'.app p).app (.boolLit b)).app H) t e)
        (if b then t.app ((ofTrue'.app p).app H) else e.app ((ofFalse'.app p).app H))

/-- The types the predicate takes, outermost first. -/
def ConditionImpl.domain : ConditionImpl → List VExpr
  | .bool => [.bool]
  | .reflectNatNat .. => [.nat, .nat]

structure ReflectNatNat.WF
    (c : VContext) (asBool : Expr) (reflect : Reflection) (proof : Expr) where
  (asBool' proof' : VExpr)
  hreflect : Reflection.WF c reflect
  hAsBool : c.TrExprS asBool asBool'
  hProof : c.TrExprS proof proof'

def ConditionImpl.WF (c : VContext) : ConditionImpl → Type
  | .bool => Unit
  | .reflectNatNat asBool reflect proof => ReflectNatNat.WF c asBool reflect proof

/-- A `Condition` together with its translation. The one field beyond the translations is
`Condition.check`'s unconditional part: the predicate has the arity the `impl` fixes. -/
structure Condition.WF (c : VContext) (cond : Condition) where
  (prop' dec' : VExpr)
  himpl : cond.impl.WF c
  hprop : c.TrExprS cond.prop prop'
  hdec : c.TrExprS cond.dec dec'
  /-- The predicate is a proposition at arguments of the types the `impl` fixes. Applied rather
  than as an arity, because applied is what the checks give: for a `reflectNatNat` the only
  thing that types `prop` is the gadget `e`, which mentions it only as `prop x y` under its own
  two binders. `prop` itself being a function of two `Nat`s is stronger, not derivable from
  that, and not something a consumer -- which only ever applies it -- has any use for. -/
  propT : ∀ (E : c.Ext) {Γ : List VExpr}, OnCtx Γ (E.venv.IsType c.lparams.length) →
    ∀ {args : List VExpr}, VExpr.ArgsTyped E.venv c.lparams.length Γ cond.impl.domain .id args →
    E.venv.HasType c.lparams.length Γ (prop'.appN args) (.sort .zero)
  /-- The check ran before any binder. Everything above is therefore stated at `[]`, which is what
  lets a consumer move it to whatever context it has built up: `TrExprS.of_nil` for the
  translations, `HasType.weak0` for the typings. Without this the fields would be facts about a
  context nobody else has, since `c.withMLC` *replaces* the local context rather than extending
  it. `Condition.check.WF` has it as a hypothesis, so recording it here costs nothing. -/
  vnil : c.vlctx = []

/-! The two translations at `[]`, which is where `vnil` puts them, and the closedness that
follows: a condition is checked before any binder, so a closing never reaches its pieces. -/

theorem Condition.WF.hprop0 {cnd : Condition} (w : Condition.WF c cnd) :
    TrExprS c.venv c.lparams [] cnd.prop w.prop' := by rw [← w.vnil]; exact w.hprop

theorem Condition.WF.hdec0 {cnd : Condition} (w : Condition.WF c cnd) :
    TrExprS c.venv c.lparams [] cnd.dec w.dec' := by rw [← w.vnil]; exact w.hdec

theorem Condition.WF.propC {cnd : Condition} (w : Condition.WF c cnd) : w.prop'.ClosedN :=
  w.hprop0.closedN_nil c.Ewf.ordered

theorem Condition.WF.decC {cnd : Condition} (w : Condition.WF c cnd) : w.dec'.ClosedN :=
  w.hdec0.closedN_nil c.Ewf.ordered

/-- When the decision procedure is known to evaluate, which is the only hypothesis `WF_ite` and
`WF_dite` take beyond well-typedness. This is where the three conditions differ: `.bool`
decides its own scrutinee, while a `reflectNatNat` decides by `asBool`, which the guards on the
branches that use it make a reflected primitive (`Nat.ble`, `Nat.beq`). -/
def ConditionImpl.WF.apply : ∀ {cond}, ConditionImpl.WF c cond → List VExpr → VExpr → Prop
  | .bool, _, args, v => args = [v]
  | .reflectNatNat .., H, args, v => v = H.asBool'.appN args

/-- The extra content of `Condition.check` at `ite := true`: `Condition.ite` at translated,
well-typed pieces translates, and to the `iteApp` of the condition's own pieces on the nose --
the same shape `WF_dite` has. Naming the translation rather than existentially quantifying it is
what lets `IteEval` be the *only* evaluation statement: a caller that built its conditional here
and one that reached an `iteApp` by closing off probe variables are asking about the same term,
so there is no reason for the two to have separate equations.

Positive rather than an elimination: the caller is *building* the equation body out of these,
and gets to assemble its translation from the pieces instead of taking one apart afterwards.
`Condition.decide` is `ite` at `Bool`, so it needs no clause of its own.

Quantified over an arbitrary well-formed `MLCtx`, not stated at `c`. Being positive is exactly
what forces this: the callers apply it to *their* pieces, and those live past whatever binders
they have opened -- the `eager` gadget's conditional is compared under a `withLocalDecl` and a
probe, so its `args` and branches mention fvars that do not exist at `c`. A `c`-level statement
could not be transported to them, since weakening moves a fixed term into a bigger context and
these terms are not in the smaller one. The burden lands on `Condition.check.WF`, which has it
either way: the pieces it supplies itself (`cnd.prop`, `cnd.dec`) are closed by `Condition.OK`,
so `TrExprS.weakFV_inv` and `TrExprS.of_nil` move them to any context.

The sort of `α` is asked for only when `natOnly` is false, and that is not a convenience. Nothing
in the model pins `Nat`'s universe: `HasPrimitives` records that the constructors are present,
not the declared type, and a bogus environment could put `Nat` at any sort, so no caller at
`α = Nat` can produce `Nat : Type 0`. The `natOnly` case does not need it -- it reads the whole
`ite` off the `checkType natITE` check, which the checker ran at `Nat` -- while a `reflectNatNat`
instantiates `checkITE`'s `∀ α : Type, α → α → α` and genuinely does. -/
def Condition.WF.WF_ite {cnd : Condition} (w : Condition.WF c cnd) (natOnly := false) : Prop :=
  ∀ {m : MLCtx} [c.MLCWF m] {α t e args α' t' e' args'},
    (c.withMLC m).TrExprS α α' →
    (natOnly = false → (c.withMLC m).HasType α' (.sort (.succ .zero))) →
    (natOnly → α = q(Nat)) →
    args.toList.Forall₂ (c.withMLC m).TrExprS args' →
    List.Forall₂ (c.withMLC m).HasType args' cnd.impl.domain →
    (c.withMLC m).TrExprS t t' → (c.withMLC m).HasType t' α' →
    (c.withMLC m).TrExprS e e' → (c.withMLC m).HasType e' α' →
    (c.withMLC m).TrExprS (cnd.ite α args t e)
      (iteApp α' (w.prop'.appN args') (w.dec'.appN args') t' e')

/-- The extra content of `Condition.check` at `dite := true`, in the same positive form. The
branches are functions of the decision -- `Nat.mod` and `Nat.div` really do use it, as the
`1 ≤ y` argument to `go` -- so they are translated under a binder and the conclusion
instantiates them.

The proof is existential. The caller never inspects it, proof irrelevance makes any proof of
the decided proposition do, and which one the checker produces depends on the `Reflection`'s
`ofTrue`/`ofFalse`; naming it here would leak those into every use site. -/
def Condition.WF.WF_dite {cnd : Condition} (w : Condition.WF c cnd) : Prop :=
  ∀ {m : MLCtx} [c.MLCWF m] {t e args P t' e' args'},
    args.toList.Forall₂ (c.withMLC m).TrExprS args' →
    List.Forall₂ (c.withMLC m).HasType args' cnd.impl.domain →
    (c.withMLC m).TrExprS (mkAppN cnd.prop args) P → (c.withMLC m).HasType P (.sort .zero) →
    TrExprS c.venv c.lparams ((none, .vlam P) :: (c.withMLC m).vlctx) t t' →
    c.venv.HasType c.lparams.length (P :: (c.withMLC m).vlctx.toCtx) t' .nat →
    TrExprS c.venv c.lparams ((none, .vlam (vexpr(Not).app P)) :: (c.withMLC m).vlctx) e e' →
    c.venv.HasType c.lparams.length (vexpr(Not).app P :: (c.withMLC m).vlctx.toCtx) e' .nat →
    (c.withMLC m).TrExprS (cnd.dite args t e)
      (diteApp P (w.dec'.appN args') (.lam P t') (.lam (vexpr(Not).app P) e'))

/-- `WF_dite` at the level of the model: the same equation, about a `diteApp` the caller has
already built out of the condition's `prop` and `dec` rather than about `Condition.dite`'s
translation.

A caller that *builds* its conditional as an `Expr` wants `WF_dite`. The fuel recursions want
this: they reach their conditionals by closing off the checker's probe variables, and a closing
acts on `VExpr`s, so by then there is no `Expr` left to talk about. The branches are functions
rather than open terms for the same reason -- that is what a closed `Condition.dite` substitutes
to. -/
def Condition.WF.DiteEval {cnd : Condition} (w : Condition.WF c cnd) : Prop :=
  ∀ (E : c.Ext) ⦃Γ : List VExpr⦄ {args' : List VExpr} {t' e' be : VExpr} (b : Bool),
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    List.Forall₂ (E.venv.HasType c.lparams.length Γ) args' cnd.impl.domain →
    w.himpl.apply args' be →
    E.venv.IsDefEqU c.lparams.length Γ be (.boolLit b) →
    VExpr.WF E.venv c.lparams.length Γ (diteApp (w.prop'.appN args') (w.dec'.appN args') t' e') →
    ∃ pf, E.venv.IsDefEqU c.lparams.length Γ
      (diteApp (w.prop'.appN args') (w.dec'.appN args') t' e')
      (if b then t'.app pf else e'.app pf)

/-- The `ite` equation, exactly as `DiteEval` is to `WF_dite`: the conditional built out of the
condition's own `prop` and `dec` collapses to the branch its decision selects. This is the only
`ite` evaluation there is. `WF_ite` names the term a source-level caller built, and this says
what that term is worth, wherever it has since been carried to -- `Nat.mod`'s outer conditional
is reached by closing off probe variables, and `Nat.bitwise`'s operator only decides once a
closing has instantiated it, so neither is still an `Expr` by the time it is evaluated.

`natOnly` restricts it to `α' = Nat`, for the same reason it restricts `WF_ite`: the `.bool`
condition reads its whole conditional off the `checkType natITE` check, which the checker ran at
`Nat`, so that is the only type it can speak about. A `reflectNatNat` instantiates `checkITE`'s
`∀ α : Type, α → α → α` and is unrestricted -- which is what `Condition.decide`, an `ite` at
`Bool`, needs. -/
def Condition.WF.IteEval {cnd : Condition} (w : Condition.WF c cnd) (natOnly := false) : Prop :=
  ∀ (E : c.Ext) ⦃Γ : List VExpr⦄ {args' : List VExpr} {α' t' e' be : VExpr} (b : Bool),
    (natOnly → α' = .nat) →
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    List.Forall₂ (E.venv.HasType c.lparams.length Γ) args' cnd.impl.domain →
    w.himpl.apply args' be →
    E.venv.IsDefEqU c.lparams.length Γ be (.boolLit b) →
    VExpr.WF E.venv c.lparams.length Γ (iteApp α' (w.prop'.appN args') (w.dec'.appN args') t' e') →
    E.venv.IsDefEqU c.lparams.length Γ
      (iteApp α' (w.prop'.appN args') (w.dec'.appN args') t' e') (if b then t' else e')

/-- The decision procedure is well typed at arguments of the `impl`'s domain types. Nothing else
says so: `Condition.WF` records `dec`'s translation, and what types it is the reflection's
`toDec`, through the `e ≡ dec` check. A caller that builds a conditional out of `dec` needs
this, and a caller that takes one apart needs it to name the pieces. -/
def Condition.WF.DecT {cnd : Condition} (w : Condition.WF c cnd) : Prop :=
  ∀ (E : c.Ext) ⦃Γ : List VExpr⦄ {args' : List VExpr},
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    List.Forall₂ (E.venv.HasType c.lparams.length Γ) args' cnd.impl.domain →
    VExpr.WF E.venv c.lparams.length Γ (w.dec'.appN args')

/-- No projections, which is what `TrExprS.IsUnique` amounts to and what makes the above usable.
Decidable, so every `Condition` in the checker discharges it by computation like the rest of
`CondOK`. -/
def noProj : Expr → Bool
  | .app f a => noProj f && noProj a
  | .lam _ t b _ => noProj t && noProj b
  | .forallE _ t b _ => noProj t && noProj b
  | .letE _ t v b _ => noProj t && noProj v && noProj b
  | .mdata _ e => noProj e
  | .proj .. => false
  | _ => true

theorem noProj.isUnique {e : Expr} : noProj e → TrExprS.IsUnique e := by
  induction e <;> simp_all [noProj, TrExprS.IsUnique]

/-- The side conditions the checks carry on every piece of the condition: no free variables
outside the context, which is what `checkType` demands, and no loose bound variables.

The second is not decoration. In the `reflectNatNat` case `checkType` is run on `e`, which has
`cond.prop` under two `Nat` binders, and `inferType cond.prop` then runs back down in the
context the check started in; bringing the translation down is `TrExprS.weakFV_inv`, whose
`Closed e dk` hypothesis is exactly this. Every `Condition` the checker uses is a closed
constant, so both are discharged by computation at each call site. -/
def CondOK (e : Expr) : Bool :=
  !e.hasFVar' && !e.hasLevelMVar' && !e.hasExprMVar' && e.looseBVarRange' == 0 && noProj e

def ConditionImpl.OK : ConditionImpl → Bool
  | .bool => true
  | .reflectNatNat asBool reflect proof =>
    CondOK asBool && CondOK proof && CondOK reflect.type && CondOK reflect.toDec &&
    CondOK reflect.ofTrue && CondOK reflect.ofFalse &&
    CondOK reflect.ite && CondOK reflect.natDITE

class Condition.OK (cond : Condition) : Prop where
  prop : CondOK cond.prop
  dec : CondOK cond.dec
  impl : cond.impl.OK

theorem ConditionImpl.OK.reflect {asBool proof : Expr} {reflect : Reflection}
    (h : (ConditionImpl.reflectNatNat asBool reflect proof).OK) :
    CondOK asBool ∧ CondOK proof ∧ CondOK reflect.type ∧ CondOK reflect.toDec ∧
    CondOK reflect.ofTrue ∧ CondOK reflect.ofFalse ∧ CondOK reflect.ite ∧
    CondOK reflect.natDITE := by
  simpa only [ConditionImpl.OK, Bool.and_eq_true, and_assoc] using h

theorem CondOK.fvarsIn {P} {e : Expr} (h : CondOK e) : FVarsIn P e := by
  simp only [CondOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact .of_hasFVar h.1.1.1.1 h.1.1.1.2 h.1.1.2

theorem CondOK.closed {e : Expr} (h : CondOK e) : Closed e := by
  simp only [CondOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact .of_looseBVarRange_zero h.1.1.2 h.1.2

theorem CondOK.looseBVarRange {e : Expr} (h : CondOK e) : e.looseBVarRange' = 0 := by
  simp only [CondOK, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

theorem CondOK.noProj {e : Expr} (h : CondOK e) : noProj e := by
  simp only [CondOK, Bool.and_eq_true] at h; exact h.2

theorem CondOK.isUnique {e : Expr} (h : CondOK e) : TrExprS.IsUnique e :=
  noProj.isUnique (CondOK.noProj h)

/-- What `WF_ite` and `WF_dite` need at literal arguments: the decision value they quantify over
is the condition's `asBool` at those literals, so a reflected `asBool` evaluates it.

Containment comes from the translation rather than from a guard on the branch -- a constant only
translates if it is in the environment -- which is why none of the branches using a `Condition`
name its `asBool` in their guards. -/
theorem ReflectNatNat.WF.apply_lit {c : VContext} {fc : Name} {f : Nat → Nat → Bool}
    {reflect proof} (W : ReflectNatNat.WF c (.const fc []) reflect proof)
    (H : c.venv.ReflectsNatNatBool fc f) (a b : Nat) :
    c.IsDefEqU (W.asBool'.appN [.natLit a, .natLit b]) (.boolLit (f a b)) := by
  -- a `.const` translates only one way, and only when it is in the environment
  obtain ⟨_, _, _, hAsBool, _⟩ := W
  let .const (ci := ci) hci hus _ := hAsBool
  simp at hus; subst hus
  simpa [VExpr.appN] using TypeChecker.VContext.natBinLitBool H ⟨ci, hci⟩ a b

/-- The two conditions that decide by a reflected primitive, at literal arguments. `Condition.WF`
is otherwise generic in the `impl`; this is where a branch commits to which one it ran. -/
theorem Condition.WF.natLE_apply {c : VContext} (w : Condition.WF c Condition.natLE)
    (hprim : c.venv.HasPrimitives) {be : VExpr} (a b : Nat)
    (hbe : w.himpl.apply [.natLit a, .natLit b] be) :
    c.IsDefEqU be (.boolLit (Nat.ble a b)) :=
  hbe ▸ w.himpl.apply_lit hprim.natBLE a b

theorem Condition.WF.natEq_apply {c : VContext} (w : Condition.WF c Condition.natEq)
    (hprim : c.venv.HasPrimitives) {be : VExpr} (a b : Nat)
    (hbe : w.himpl.apply [.natLit a, .natLit b] be) :
    c.IsDefEqU be (.boolLit (Nat.beq a b)) :=
  hbe ▸ w.himpl.apply_lit hprim.natBEq a b

/-- The two decisions at literal arguments, in the extension a closed-off equation is read in.
The condition was checked before any binder, so `vnil` is what moves it to the empty context. -/
theorem Condition.WF.natLE_apply₀ {c : VContext} (w : Condition.WF c Condition.natLE)
    (hprim : c.venv.HasPrimitives) (E : c.Ext) {be : VExpr} (a b : Nat)
    (hbe : w.himpl.apply [.natLit a, .natLit b] be) :
    E.IsDefEqU₀ be (.boolLit (Nat.ble a b)) := by
  have h := E.mono (w.natLE_apply hprim a b hbe)
  rw [w.vnil] at h; exact h

theorem Condition.WF.natEq_apply₀ {c : VContext} (w : Condition.WF c Condition.natEq)
    (hprim : c.venv.HasPrimitives) (E : c.Ext) {be : VExpr} (a b : Nat)
    (hbe : w.himpl.apply [.natLit a, .natLit b] be) :
    E.IsDefEqU₀ be (.boolLit (Nat.beq a b)) := by
  have h := E.mono (w.natEq_apply hprim a b hbe)
  rw [w.vnil] at h; exact h

instance : Condition.bool.OK := ⟨rfl, rfl, rfl⟩
instance : Condition.natLE.OK := ⟨rfl, rfl, rfl⟩
instance : Condition.natEq.OK := ⟨rfl, rfl, rfl⟩

/-! The closed types and terms the `.bool` branch of `Condition.check` compares against. These
are built rather than read off anything: `isDefEq.WF` relates the *translations* of the two
expressions it was given, so a caller has to name the translation it expects on the right. -/

/-- `Bool → Prop`, the type the predicate is checked against. -/
theorem TrExprS.boolProp (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    TrExprS env Us Δ (.forallE n q(Bool) q(Prop) bi) vexpr(Bool → Prop) :=
  (TrTy.forallE (.of (hprim.trBool henv hbool) (hprim.boolIsType henv hbool hΔ))
    (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)).trS

/-! ### Transport to a context with more binders *outside*

`TrExprS.of_nil` moves a `[]`-level translation to another context, but only one with no bound
variables: `VLCtx.FVLift` extends by free variables. The reflection's checks are run at terms
whose binders are *bound*, so the same closed subterm (`toDec`, `type`) is read once at `[]` and
once four binders deep, and nothing identifies the two readings.

Appending on the right is the missing move. It adds binders *outside* everything, so no de Bruijn
index shifts and the translation is unchanged: `find?` returns before it reaches the appended
part, and the typing side conditions weaken by `IsDefEq.weakR`. -/

@[simp] theorem VLCtx.toCtx_append : ∀ (Δ Δ' : VLCtx), (Δ ++ Δ').toCtx = Δ.toCtx ++ Δ'.toCtx
  | [], _ => rfl
  | (_, .vlam _) :: Δ, Δ' => congrArg _ (VLCtx.toCtx_append Δ Δ')
  | (_, .vlet ..) :: Δ, Δ' => VLCtx.toCtx_append Δ Δ'

/-- A lookup that lands in the prefix does not reach the rest of the context. The converse of
`find?_append`, restricted to the bound variables the prefix binds -- which is every bound
variable a closed term has. -/
theorem VLCtx.find?_append_inv : ∀ {Δ Δ' : VLCtx} {i r}, i < Δ.bvars →
    (Δ ++ Δ').find? (.inl i) = some r → Δ.find? (.inl i) = some r
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | (ofv, d) :: Δ, Δ', i, r, hi => by
    simp only [VLCtx.find?, List.cons_append]
    match ofv, i with
    | none, 0 => simp only [VLCtx.next]; exact id
    | none, i+1 =>
      simp only [VLCtx.next, VLCtx.bvars] at hi ⊢
      cases hf : VLCtx.find? (Δ ++ Δ') (.inl i) with
      | none => simp
      | some p => rw [VLCtx.find?_append_inv (Nat.lt_of_succ_lt_succ hi) hf]; simp
    | some _, i =>
      simp only [VLCtx.next, VLCtx.bvars] at hi ⊢
      cases hf : VLCtx.find? (Δ ++ Δ') (.inl i) with
      | none => simp
      | some p => rw [VLCtx.find?_append_inv hi hf]; simp

theorem VLCtx.find?_append : ∀ {Δ Δ' : VLCtx} {v r}, Δ.find? v = some r →
    (Δ ++ Δ').find? v = some r
  | [], _, _, _, h => by simp [VLCtx.find?] at h
  | (ofv, d) :: Δ, Δ', v, r, h => by
    revert h
    simp only [VLCtx.find?, List.cons_append]
    split <;> [exact id; rename_i v' _]
    cases hf : VLCtx.find? Δ v' with
    | none => simp
    | some p => simp [VLCtx.find?_append hf]

/-- Literals unfold to constructor applications, which have no projections either. -/
theorem noProj_toConstructor : ∀ {l : Literal}, noProj l.toConstructor
  | .natVal n => by cases n <;> rfl
  | .strVal s => by
    simp only [Literal.toConstructor, Expr.strLitToConstructor, noProj]
    induction s.toList <;> simp [noProj, *]

/-- A translation survives binders appended on the right. `noProj` only to sidestep `proj`, whose
`TrProj` side condition would have to be transported too; every closed piece a `Condition` carries
is projection-free by `CondOK`. -/
theorem TrExprS.weakR {env : VEnv} {Us : List Name} (henv : env.Ordered) {Δ' : VLCtx} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, TrExprS env Us Δ e e' →
      OnCtx Δ.toCtx (env.IsType Us.length) → noProj e →
      TrExprS env Us (Δ ++ Δ') e e' := by
  have weakT : ∀ {Δ : VLCtx} {x A}, OnCtx Δ.toCtx (env.IsType Us.length) →
      env.HasType Us.length Δ.toCtx x A → env.HasType Us.length (Δ ++ Δ').toCtx x A := by
    intro Δ x A hΔ h
    have h2 : env.HasType Us.length (Δ.toCtx ++ Δ'.toCtx) x A :=
      VEnv.IsDefEq.weakR henv (VEnv.CtxWF.closed henv hΔ) h Δ'.toCtx
    simpa using h2
  have weakI : ∀ {Δ : VLCtx} {A}, OnCtx Δ.toCtx (env.IsType Us.length) →
      env.IsType Us.length Δ.toCtx A → env.IsType Us.length (Δ ++ Δ').toCtx A :=
    fun hΔ ⟨_, h⟩ => ⟨_, weakT hΔ h⟩
  intro Δ e e' H
  induction H with
  | bvar h => intro _ _; exact .bvar (VLCtx.find?_append h)
  | fvar h => intro _ _; exact .fvar (VLCtx.find?_append h)
  | sort h => intro _ _; exact .sort h
  | const h1 h2 h3 => intro _ _; exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    intro hΔ hu
    simp only [noProj, Bool.and_eq_true] at hu
    exact .app (weakT hΔ h1) (weakT hΔ h2) (ih1 hΔ hu.1) (ih2 hΔ hu.2)
  | lam h1 _ _ ih1 ih2 =>
    intro hΔ hu
    simp only [noProj, Bool.and_eq_true] at hu
    exact .lam (weakI hΔ h1) (ih1 hΔ hu.1)
      (ih2 (show OnCtx (_ :: _) _ from ⟨hΔ, h1⟩) hu.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    intro hΔ hu
    simp only [noProj, Bool.and_eq_true] at hu
    have hΔ1 : OnCtx (_ :: _) (env.IsType Us.length) := ⟨hΔ, h1⟩
    exact .forallE (weakI hΔ h1) (weakI (Δ := (none, .vlam _) :: _) hΔ1 h2)
      (ih1 hΔ hu.1) (ih2 hΔ1 hu.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    intro hΔ hu
    simp only [noProj, Bool.and_eq_true] at hu
    exact .letE (weakT hΔ h1) (ih1 hΔ hu.1.1) (ih2 hΔ hu.1.2) (ih3 hΔ hu.2)
  | lit h1 _ ih => intro hΔ _; exact .lit h1 (ih hΔ noProj_toConstructor)
  | mdata _ ih => intro hΔ hu; exact .mdata (ih hΔ (by simpa [noProj] using hu))
  | proj _ _ _ => intro _ hu; simp [noProj] at hu

/-- **A closed term is read the same way wherever it is read.** `weakR` adds context to a
reading; this removes it, which is the direction every closed piece of a `Condition` needs.
`Condition.check` reads them under the gadget's binders, `Reflection.checkITE` under its own, and
only a reading at the base context can identify the two -- so with this, no check has to exist
merely to produce that reading.

The prefix `pre` is what the term's *own* binders push, so it is shared by the two sides and its
shape is never inspected: a lookup either lands in it, and then agrees on both sides, or the term
was not closed. What does have to travel is the typing side conditions, which live at the wider
context; they come down by `weakN_iff`, which needs the subterm closed, so closedness is proved
in the same induction. The types those side conditions carry are *not* preserved, and need not
be -- `TrExprS` quantifies them existentially, so re-deriving some type at the narrower context
is enough, which `app_inv`/`lam_inv` do from the node's own well-formedness. -/
theorem TrExprS.ofClosed {env : VEnv} {Us : List Name} (henv : VEnv.WF env) {Δ : VLCtx} :
    ∀ {Δ₀ : VLCtx} {e : Expr} {e' : VExpr}, TrExprS env Us Δ₀ e e' →
      ∀ {pre : VLCtx}, Δ₀ = pre ++ Δ →
      noProj e → Closed e pre.bvars → FVarsIn (fun _ => False) e →
      CtxClosed pre.toCtx →
      (∀ {v : Nat ⊕ FVarId} {x A}, pre.find? v = some (x, A) → x.ClosedN pre.toCtx.length) →
      OnCtx (pre ++ Δ).toCtx (env.IsType Us.length) →
      VExpr.WF env Us.length (pre ++ Δ).toCtx e' →
      e'.ClosedN pre.toCtx.length ∧ TrExprS env Us pre e e' := by
  -- the narrower context is well formed, and what is closed at it does not see the rest
  have narrow : ∀ {pre : VLCtx}, CtxClosed pre.toCtx →
      OnCtx (pre ++ Δ).toCtx (env.IsType Us.length) →
      OnCtx pre.toCtx (env.IsType Us.length) := fun hcc hΔ =>
    OnCtx.weakN_inv henv (Ctx.LiftN.right hcc Δ.toCtx) (by simpa using hΔ)
  have wfT : ∀ {pre : VLCtx} {x : VExpr}, CtxClosed pre.toCtx → x.ClosedN pre.toCtx.length →
      OnCtx (pre ++ Δ).toCtx (env.IsType Us.length) →
      VExpr.WF env Us.length (pre ++ Δ).toCtx x → VExpr.WF env Us.length pre.toCtx x := by
    intro pre x hcc hcl hΔ hwf
    refine (VExpr.WF.weakN_iff henv (by simpa using hΔ) (Ctx.LiftN.right hcc Δ.toCtx)).1 ?_
    rw [hcl.liftN_eq (Nat.le_refl _)]; simpa using hwf
  have isTypeT : ∀ {pre : VLCtx} {A : VExpr}, CtxClosed pre.toCtx → A.ClosedN pre.toCtx.length →
      OnCtx (pre ++ Δ).toCtx (env.IsType Us.length) →
      env.IsType Us.length (pre ++ Δ).toCtx A → env.IsType Us.length pre.toCtx A := by
    intro pre A hcc hcl hΔ h
    refine (VEnv.IsType.weakN_iff henv (by simpa using hΔ) (Ctx.LiftN.right hcc Δ.toCtx)).1 ?_
    rw [hcl.liftN_eq (Nat.le_refl _)]; simpa using h
  have hasTypeT : ∀ {pre : VLCtx} {x A : VExpr}, CtxClosed pre.toCtx →
      x.ClosedN pre.toCtx.length → A.ClosedN pre.toCtx.length →
      OnCtx (pre ++ Δ).toCtx (env.IsType Us.length) →
      env.HasType Us.length (pre ++ Δ).toCtx x A → env.HasType Us.length pre.toCtx x A := by
    intro pre x A hcc hcx hcA hΔ h
    refine (VEnv.HasType.weakN_iff henv (by simpa using hΔ) (Ctx.LiftN.right hcc Δ.toCtx)).1 ?_
    rw [hcx.liftN_eq (Nat.le_refl _), hcA.liftN_eq (Nat.le_refl _)]; simpa using h
  have isWF : ∀ {Γ : List VExpr} {A}, env.IsType Us.length Γ A →
      VExpr.WF env Us.length Γ A := fun ⟨_, h⟩ => ⟨_, h⟩
  -- and the invariant on the prefix, as it grows past one more binder
  have grow : ∀ {pre : VLCtx} {d : VLocalDecl},
      (∀ {v : Nat ⊕ FVarId} {x A}, pre.find? v = some (x, A) → x.ClosedN pre.toCtx.length) →
      d.value.ClosedN (VLCtx.toCtx ((none, d) :: pre)).length →
      ∀ {v : Nat ⊕ FVarId} {x A}, VLCtx.find? ((none, d) :: pre) v = some (x, A) →
        x.ClosedN (VLCtx.toCtx ((none, d) :: pre)).length := by
    intro pre d hpre hd v x A hv
    have hlift : ∀ {w : VExpr}, w.ClosedN pre.toCtx.length →
        (w.liftN d.depth).ClosedN (VLCtx.toCtx ((none, d) :: pre)).length := by
      intro w hw
      cases d with
      | vlam A' => exact hw.liftN
      | vlet A' v' => simpa [VLocalDecl.depth, VLCtx.toCtx] using hw
    match v with
    | .inl 0 => simp only [VLCtx.find?, VLCtx.next] at hv; obtain ⟨rfl, -⟩ := hv; exact hd
    | .inl (i+1) =>
      revert hv; simp only [VLCtx.find?, VLCtx.next]
      cases hf : pre.find? (.inl i) with
      | none => exact nofun
      | some p => intro hv; cases hv; exact hlift (hpre hf)
    | .inr fv =>
      revert hv; simp only [VLCtx.find?, VLCtx.next]
      cases hf : pre.find? (.inr fv) with
      | none => exact nofun
      | some p => intro hv; cases hv; exact hlift (hpre hf)
  have growLam : ∀ {pre : VLCtx} {A : VExpr},
      (∀ {v : Nat ⊕ FVarId} {x A}, pre.find? v = some (x, A) → x.ClosedN pre.toCtx.length) →
      ∀ {v : Nat ⊕ FVarId} {x A'}, VLCtx.find? ((none, .vlam A) :: pre) v = some (x, A') →
        x.ClosedN (VLCtx.toCtx ((none, .vlam A) :: pre)).length :=
    fun hpre => grow (d := .vlam _) hpre (Nat.succ_pos _)
  intro Δ₀ e e' H
  induction H with
  | bvar h =>
    rintro pre rfl _ hcl _ _ hpre _ _
    have h' := VLCtx.find?_append_inv hcl h
    exact ⟨hpre h', .bvar h'⟩
  | fvar h => rintro pre rfl _ _ hfv _ _ _ _; exact hfv.elim
  | sort h => rintro pre rfl _ _ _ _ _ _ _; exact ⟨trivial, .sort h⟩
  | const h1 h2 h3 => rintro pre rfl _ _ _ _ _ _ _; exact ⟨trivial, .const h1 h2 h3⟩
  | app h1 h2 _ _ ih1 ih2 =>
    rintro pre rfl hu ⟨hcl1, hcl2⟩ ⟨hfv1, hfv2⟩ hcc hpre hΔ hwf
    simp only [noProj, Bool.and_eq_true] at hu
    obtain ⟨hc1, ih1⟩ := ih1 rfl hu.1 hcl1 hfv1 hcc hpre hΔ ⟨_, h1⟩
    obtain ⟨hc2, ih2⟩ := ih2 rfl hu.2 hcl2 hfv2 hcc hpre hΔ ⟨_, h2⟩
    obtain ⟨_, _, hf, ha⟩ :=
      VExpr.WF.app_inv henv (narrow hcc hΔ) (wfT hcc ⟨hc1, hc2⟩ hΔ hwf)
    exact ⟨⟨hc1, hc2⟩, .app hf ha ih1 ih2⟩
  | lam h1 _ _ ih1 ih2 =>
    rintro pre rfl hu ⟨hcl1, hcl2⟩ ⟨hfv1, hfv2⟩ hcc hpre hΔ hwf
    simp only [noProj, Bool.and_eq_true] at hu
    obtain ⟨hc1, ih1⟩ := ih1 rfl hu.1 hcl1 hfv1 hcc hpre hΔ (isWF h1)
    obtain ⟨-, _, hb⟩ := VExpr.WF.lam_inv henv (by simpa using hΔ) hwf
    obtain ⟨hc2, ih2⟩ := ih2 (pre := (none, .vlam _) :: pre) rfl hu.2 hcl2 hfv2
      ⟨hcc, hc1⟩ (growLam hpre) (show OnCtx (_ :: _) _ from ⟨hΔ, h1⟩) ⟨_, hb⟩
    exact ⟨⟨hc1, hc2⟩, .lam (isTypeT hcc hc1 hΔ h1) ih1 ih2⟩
  | forallE h1 h2 _ _ ih1 ih2 =>
    rintro pre rfl hu ⟨hcl1, hcl2⟩ ⟨hfv1, hfv2⟩ hcc hpre hΔ hwf
    simp only [noProj, Bool.and_eq_true] at hu
    obtain ⟨hc1, ih1⟩ := ih1 rfl hu.1 hcl1 hfv1 hcc hpre hΔ (isWF h1)
    obtain ⟨hc2, ih2⟩ := ih2 (pre := (none, .vlam _) :: pre) rfl hu.2 hcl2 hfv2
      ⟨hcc, hc1⟩ (growLam hpre) (show OnCtx (_ :: _) _ from ⟨hΔ, h1⟩) (isWF h2)
    refine ⟨⟨hc1, hc2⟩, .forallE (isTypeT hcc hc1 hΔ h1) ?_ ih1 ih2⟩
    exact isTypeT (pre := (none, .vlam _) :: pre) ⟨hcc, hc1⟩ hc2
      (show OnCtx (_ :: _) _ from ⟨hΔ, h1⟩) h2
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    rintro pre rfl hu ⟨hcl1, hcl2, hcl3⟩ ⟨hfv1, hfv2, hfv3⟩ hcc hpre hΔ hwf
    simp only [noProj, Bool.and_eq_true] at hu
    obtain ⟨hc1, ih1⟩ := ih1 rfl hu.1.1 hcl1 hfv1 hcc hpre hΔ
      (isWF (h1.isType henv (by simpa using hΔ)))
    obtain ⟨hc2, ih2⟩ := ih2 rfl hu.1.2 hcl2 hfv2 hcc hpre hΔ ⟨_, h1⟩
    obtain ⟨hc3, ih3⟩ := ih3 (pre := (none, .vlet _ _) :: pre) rfl hu.2 hcl3 hfv3
      (by simpa [VLCtx.toCtx] using hcc)
      (grow (d := .vlet _ _) hpre (by simpa [VLocalDecl.value, VLCtx.toCtx] using hc2))
      (by simpa [VLCtx.toCtx] using hΔ) (by simpa [VLCtx.toCtx] using hwf)
    exact ⟨by simpa [VLCtx.toCtx] using hc3,
      .letE (hasTypeT hcc hc2 hc1 hΔ h1) ih1 ih2 (by simpa [VLCtx.toCtx] using ih3)⟩
  | lit h1 _ ih =>
    rintro pre rfl _ _ _ hcc hpre hΔ hwf
    obtain ⟨hc, ih⟩ := ih rfl noProj_toConstructor .toConstructor .toConstructor
      hcc hpre hΔ hwf
    exact ⟨hc, .lit h1 ih⟩
  | mdata _ ih =>
    rintro pre rfl hu hcl hfv hcc hpre hΔ hwf
    obtain ⟨hc, ih⟩ := ih rfl (by simpa [noProj] using hu) hcl hfv hcc hpre hΔ hwf
    exact ⟨hc, .mdata ih⟩
  | proj _ _ _ => rintro pre rfl hu _ _ _ _ _ _; simp [noProj] at hu

/-- A `[]`-level translation is *the* translation, at every context at once. This is what
identifies the readings of a closed piece that different checks produce at their own depths. -/
theorem TrExprS.of_nil_any {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (henv : env.Ordered) (hu : noProj e) (H₀ : TrExprS env Us [] e e') :
    TrExprS env Us Δ e e' := by simpa using TrExprS.weakR henv H₀ trivial hu

theorem TrExprS.of_nil_unique {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e₁ e₂ : VExpr}
    (henv : env.Ordered) (hu : noProj e)
    (H₀ : TrExprS env Us [] e e₁) (H : TrExprS env Us Δ e e₂) : e₂ = e₁ :=
  TrExprS.unique' .base (noProj.isUnique hu) H (TrExprS.of_nil_any henv hu H₀)

/-- A closed head at two arguments: the head translates the one way it can, so what is left of
the translation is the arguments'. This is how a condition's `prop` or `dec` is recognised
wherever a checked conditional has been carried to. -/
theorem TrExprS.app2_nil_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {hd A B : Expr}
    {hd' P : VExpr} (henv : env.Ordered) (hu : noProj hd) (H₀ : TrExprS env Us [] hd hd')
    (H : TrExprS env Us Δ (mkAppN hd #[A, B]) P) :
    ∃ a' b', TrExprS env Us Δ A a' ∧ TrExprS env Us Δ B b' ∧ P = (hd'.app a').app b' := by
  rw [Expr.mkAppN_eq] at H
  cases (by simpa [Expr.appN] using H : TrExprS env Us Δ ((hd.app A).app B) P) with | app _ _ hf hB
  cases hf with | app _ _ hhd hA
  cases TrExprS.of_nil_unique henv hu H₀ hhd
  exact ⟨_, _, hA, hB, rfl⟩

/-- The same at one argument, which is the arity of the `bool` condition. -/
theorem TrExprS.app1_nil_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {hd A : Expr}
    {hd' P : VExpr} (henv : env.Ordered) (hu : noProj hd) (H₀ : TrExprS env Us [] hd hd')
    (H : TrExprS env Us Δ (mkAppN hd #[A]) P) :
    ∃ a', TrExprS env Us Δ A a' ∧ P = hd'.app a' := by
  rw [Expr.mkAppN_eq] at H
  cases (by simpa [Expr.appN] using H : TrExprS env Us Δ (hd.app A) P) with | app _ _ hhd hA
  cases TrExprS.of_nil_unique henv hu H₀ hhd
  exact ⟨_, hA, rfl⟩

/-- The predicate of a condition, at the two arguments every use of one applies it to. -/
theorem Condition.WF.prop_app2_inv (w : Condition.WF c cnd) [hOK : cnd.OK]
    (H : TrExprS c.venv c.lparams Δ (mkAppN cnd.prop #[A, B]) P) :
    ∃ a' b', TrExprS c.venv c.lparams Δ A a' ∧ TrExprS c.venv c.lparams Δ B b' ∧
      P = (w.prop'.app a').app b' :=
  TrExprS.app2_nil_inv c.Ewf (CondOK.noProj hOK.prop) w.hprop0 H

/-- The decision procedure, likewise. -/
theorem Condition.WF.dec_app2_inv (w : Condition.WF c cnd) [hOK : cnd.OK]
    (H : TrExprS c.venv c.lparams Δ (mkAppN cnd.dec #[A, B]) D) :
    ∃ a' b', TrExprS c.venv c.lparams Δ A a' ∧ TrExprS c.venv c.lparams Δ B b' ∧
      D = (w.dec'.app a').app b' :=
  TrExprS.app2_nil_inv c.Ewf (CondOK.noProj hOK.dec) w.hdec0 H

/-! Bound variables of a `vlam` telescope translate to themselves. The reflection's checks are
run at terms with binders four deep, so these are the leaves of every translation below. -/

theorem _root_.Lean4Lean.TrExprS.bvar0 :
    TrExprS env Us ((none, .vlam A) :: Δ) (.bvar 0) (.bvar 0) := .bvar rfl

theorem _root_.Lean4Lean.TrExprS.bvar1 :
    TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: Δ) (.bvar 1) (.bvar 1) := .bvar rfl

theorem _root_.Lean4Lean.TrExprS.bvar2 :
    TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: (none, .vlam C) :: Δ)
      (.bvar 2) (.bvar 2) := .bvar rfl

theorem _root_.Lean4Lean.TrExprS.bvar3 :
    TrExprS env Us ((none, .vlam A) :: (none, .vlam B) :: (none, .vlam C) :: (none, .vlam D) :: Δ)
      (.bvar 3) (.bvar 3) := .bvar rfl

/-- The same as a `TrTy`, so that it can sit under the binders of the type `checkITE` builds. -/
def TrTy.polyIteType : TrTy env Us Δ (.forallE n₁ q(Type)
    (.forallE n₂ (.bvar 0) (.forallE n₃ (.bvar 1) (.bvar 2) bi₃) bi₂) bi₁) :=
  .forallE (.of (.sort rfl) ⟨_, .sort (l := .succ .zero) trivial⟩) <|
  .forallE (.of .bvar0 ⟨_, .bvar .zero⟩) <|
  .forallE (.of .bvar1 ⟨_, .bvar (.succ .zero)⟩) <|
  .of .bvar2 ⟨_, .bvar (.succ (.succ .zero))⟩

/-- `∀ α : Type, α → α → α`, the type `checkITE` compares the conditional against. Written out
rather than quoted: the binder names in a quotation are hygienic, so a second quotation of the
same text is a *different* expression from the checker's. -/
theorem TrExprS.polyIteType : TrExprS env Us Δ
    (.forallE n₁ q(Type)
      (.forallE n₂ (.bvar 0) (.forallE n₃ (.bvar 1) (.bvar 2) bi₃) bi₂) bi₁)
    (.forallE vexpr(Type) (.forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2)))) :=
  (TrTy.polyIteType (Us := Us) (Δ := Δ)).trS

theorem TrExprS.propBoolProp (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    TrExprS env Us Δ
      (.forallE n₁ q(Prop) (.forallE n₂ q(Bool) q(Prop) bi₂) bi₁) vexpr(Prop → Bool → Prop) :=
  (TrTy.forallE (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)
    (TrTy.forallE
      (.of (hprim.trBool henv hbool) (hprim.boolIsType henv hbool ⟨hΔ, _, .sort trivial⟩))
      (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩))).trS

/-- `Bool → Nat → Nat → Nat`, the type the conditional is checked against. -/
theorem TrExprS.boolNat3 {env : VEnv} {Us : List Name} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    {Δ : VLCtx} {n₁ n₂ n₃ bi₁ bi₂ bi₃}
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    TrExprS env Us Δ
      (.forallE n₁ q(Bool) (.forallE n₂ q(Nat) (.forallE n₃ q(Nat) q(Nat) bi₃) bi₂) bi₁)
      vexpr(Bool → Nat → Nat → Nat) :=
  have hb := hprim.boolIsType (Us := Us) henv hbool hΔ
  have h1 := hprim.natIsType' (Us := Us) henv hnat (Γ := VExpr.bool :: Δ.toCtx) ⟨hΔ, hb⟩
  have h2 := hprim.natIsType' (Us := Us) henv hnat
    (Γ := VExpr.nat :: VExpr.bool :: Δ.toCtx) ⟨⟨hΔ, hb⟩, h1⟩
  (TrTy.forallE (.of (hprim.trBool henv hbool) hb)
    (TrTy.forallE (.of (hprim.trNat henv hnat) h1)
      (TrTy.forallE (.of (hprim.trNat henv hnat) h2)
        (.of (hprim.trNat henv hnat) (hprim.natIsType' henv hnat ⟨⟨⟨hΔ, hb⟩, h1⟩, h2⟩))))).trS

/-- `Nat → Nat → Prop`, the type the `≤` that the fuel recursions guard on is checked against. -/
theorem TrExprS.natNatProp {env : VEnv} {Us : List Name} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Δ : VLCtx} {n₁ n₂ bi₁ bi₂}
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    TrExprS env Us Δ
      (.forallE n₁ q(Nat) (.forallE n₂ q(Nat) q(Prop) bi₂) bi₁) vexpr(Nat → Nat → Prop) :=
  have h1 := hprim.natIsType' (Us := Us) henv hnat hΔ
  have h2 := hprim.natIsType' (Us := Us) henv hnat (Γ := VExpr.nat :: Δ.toCtx) ⟨hΔ, h1⟩
  (TrTy.forallE (.of (hprim.trNat henv hnat) h1)
    (TrTy.forallE (.of (hprim.trNat henv hnat) h2)
      (.of (TrExprS.sort (u := .zero) (u' := .zero) rfl)
        ⟨_, .sort (l := .zero) trivial⟩))).trS

/-- `∀ y, 1 ≤ y → ∀ fuel x, succ x ≤ fuel → Nat`: the type of the fuel-driven `go` that
`Nat.div` and `Nat.mod` recurse through. `≤` is a parameter, since the checker checks it
separately and this is where the two are joined. -/
theorem TrExprS.divGoType {env : VEnv} {Us : List Name} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    {leSrc : Expr} {le' : VExpr}
    (hleTr : ∀ {Δ}, TrExprS env Us Δ leSrc le')
    (hleT : ∀ {Γ}, env.HasType Us.length Γ le' vexpr(Nat → Nat → Prop))
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    TrExprS env Us Δ
      (.forallE n₁ q(Nat)
        (.forallE n₂ (mkApp2 leSrc q(Nat.succ Nat.zero) (.bvar 0))
          (.forallE n₃ q(Nat)
            (.forallE n₄ q(Nat)
              (.forallE n₅ (mkApp2 leSrc (.app q(Nat.succ) (.bvar 0)) (.bvar 1))
                q(Nat) bi₅) bi₄) bi₃) bi₂) bi₁)
      (.forallE .nat
        (.forallE ((le'.app (.natLit 1)).app (.bvar 0))
          (.forallE .nat (.forallE .nat
            (.forallE ((le'.app (.app .natSucc (.bvar 0))).app (.bvar 1)) .nat))))) := by
  have hnatT {Γ} (h : OnCtx Γ (env.IsType Us.length)) :
      env.IsType Us.length Γ VExpr.nat := hprim.natIsType' henv hnat h
  have hzero {Δ'} : TrExprS env Us Δ' .natZero .natZero ∧
      env.HasType Us.length Δ'.toCtx .natZero .nat := TrExprS.natZero hprim hnat
  have hsucc {Δ'} : TrExprS env Us Δ' .natSucc .natSucc ∧
      env.HasType Us.length Δ'.toCtx .natSucc (.forallE .nat .nat) := TrExprS.natSucc hprim hnat
  -- `1`, as `succ zero` rather than a numeral
  have honeT {Γ} : env.HasType Us.length Γ (VExpr.natLit 1) .nat :=
    hprim.natLitT henv hnat 1 Γ
  have hsuccT {Γ} : env.HasType Us.length Γ .natSucc (.forallE .nat .nat) := by
    simpa using (TrExprS.natSucc (Us := Us) (Δ := VLCtx.ofCtx Γ) hprim hnat).2
  have honeTr {Δ'} : TrExprS env Us Δ' q(Nat.succ Nat.zero) (.natLit 1) :=
    .app hsuccT hzero.2 hsucc.1 hzero.1
  -- the contexts, one binder at a time
  have hΔ1 : OnCtx (.nat :: Δ.toCtx) (env.IsType Us.length) := ⟨hΔ, hnatT hΔ⟩
  have hb0 : env.HasType Us.length (.nat :: Δ.toCtx) (.bvar 0) .nat := .bvar .zero
  have hguard1 : env.HasType Us.length (.nat :: Δ.toCtx)
      ((le'.app (.natLit 1)).app (.bvar 0)) (.sort .zero) := .app (.app hleT honeT) hb0
  have hguard1Tr : TrExprS env Us ((none, .vlam .nat) :: Δ)
      (mkApp2 leSrc q(Nat.succ Nat.zero) (.bvar 0)) ((le'.app (.natLit 1)).app (.bvar 0)) :=
    .app (.app hleT honeT) hb0 (.app hleT honeT hleTr honeTr) .bvar0
  have hΔ2 : OnCtx (_ :: .nat :: Δ.toCtx) (env.IsType Us.length) := ⟨hΔ1, _, hguard1⟩
  have hΔ3 : OnCtx (.nat :: _) (env.IsType Us.length) := ⟨hΔ2, hnatT hΔ2⟩
  have hΔ4 : OnCtx (.nat :: _) (env.IsType Us.length) := ⟨hΔ3, hnatT hΔ3⟩
  -- the second guard, `succ x ≤ fuel`, where `x` is the innermost binder and `fuel` the next
  have hsx : env.HasType Us.length
      (.nat :: .nat :: ((le'.app (.natLit 1)).app (.bvar 0)) :: .nat :: Δ.toCtx)
      (.app .natSucc (.bvar 0)) .nat := .app hsuccT (.bvar .zero)
  have hfuel : env.HasType Us.length
      (.nat :: .nat :: ((le'.app (.natLit 1)).app (.bvar 0)) :: .nat :: Δ.toCtx)
      (.bvar 1) .nat := .bvar (.succ .zero)
  have hguard2 : env.HasType Us.length
      (.nat :: .nat :: ((le'.app (.natLit 1)).app (.bvar 0)) :: .nat :: Δ.toCtx)
      ((le'.app (.app .natSucc (.bvar 0))).app (.bvar 1)) (.sort .zero) :=
    .app (.app hleT hsx) hfuel
  have hguard2Tr : TrExprS env Us
      ((none, .vlam .nat) :: (none, .vlam .nat) ::
        (none, .vlam ((le'.app (.natLit 1)).app (.bvar 0))) :: (none, .vlam .nat) :: Δ)
      (mkApp2 leSrc (.app (.const ``Nat.succ []) (.bvar 0)) (.bvar 1))
      ((le'.app (.app .natSucc (.bvar 0))).app (.bvar 1)) :=
    .app (.app hleT hsx) hfuel (.app hleT hsx hleTr (.app hsuccT (.bvar .zero) hsucc.1 .bvar0))
      .bvar1
  have hΔ5 : OnCtx (_ :: _) (env.IsType Us.length) := ⟨hΔ4, _, hguard2⟩
  exact (TrTy.forallE (.of (hprim.trNat henv hnat) (hnatT hΔ))
    (TrTy.forallE (.of hguard1Tr ⟨_, hguard1⟩)
      (TrTy.forallE (.of (hprim.trNat henv hnat) (hnatT hΔ2))
        (TrTy.forallE (.of (hprim.trNat henv hnat) (hnatT hΔ3))
          (TrTy.forallE (.of hguard2Tr ⟨_, hguard2⟩)
            (.of (hprim.trNat henv hnat) (hnatT hΔ5))))))).trS

/-- `fun a _ : Nat => a` and `fun _ a : Nat => a`, the two branches the conditional collapses to.
Indexed by the branch so the two `isDefEq` checks are consumed by one lemma. -/
theorem TrExprS.natProj {env : VEnv} {Us : List Name} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Δ : VLCtx} {n₁ n₂ bi₁ bi₂}
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) {i : Nat} (hi : i = 0 ∨ i = 1) :
    TrExprS env Us Δ
      (.lam n₁ q(Nat) (.lam n₂ q(Nat) (.bvar i) bi₂) bi₁)
      (.lam .nat (.lam .nat (.bvar i))) ∧
    env.HasType Us.length Δ.toCtx (.lam .nat (.lam .nat (.bvar i))) vexpr(Nat → Nat → Nat) := by
  have h1 := hprim.natIsType' (Us := Us) henv hnat (Γ := Δ.toCtx) hΔ
  have h2 := hprim.natIsType' (Us := Us) henv hnat (Γ := VExpr.nat :: Δ.toCtx) ⟨hΔ, h1⟩
  have hbv : TrExprS env Us
      ((none, .vlam .nat) :: (none, .vlam .nat) :: Δ) (.bvar i) (.bvar i) ∧
      env.HasType Us.length (VExpr.nat :: VExpr.nat :: Δ.toCtx) (.bvar i) .nat := by
    obtain rfl | rfl := hi
    · exact ⟨.bvar (A := VExpr.nat) (by
        simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]),
        .bvar .zero⟩
    · exact ⟨.bvar (A := VExpr.nat) (by
        simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
          VExpr.liftN]),
        .bvar (.succ .zero)⟩
  exact ⟨.lam h1 (hprim.trNat henv hnat) (.lam h2 (hprim.trNat henv hnat) hbv.1),
    .lam h1.choose_spec (.lam h2.choose_spec hbv.2)⟩

/-- The two projections applied to both branches pick one. This is what turns the `.bool`
branch's two `isDefEq` checks into `WF_ite`'s conclusion: the check compares the conditional at a
boolean literal against a projection, and the caller's branches are what it is then applied to. -/
theorem VEnv.IsDefEqU.natProj {env : VEnv} {U Γ} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hnatT : ∀ Γ, OnCtx Γ (env.IsType U) → env.IsType U Γ VExpr.nat)
    {t e : VExpr} (htT : env.HasType U Γ t .nat) (heT : env.HasType U Γ e .nat)
    {i : Nat} (hi : i = 0 ∨ i = 1) :
    env.IsDefEqU U Γ (((VExpr.lam .nat (.lam .nat (.bvar i))).app t).app e)
      (if i = 1 then t else e) := by
  obtain ⟨u0, hu0⟩ := hnatT Γ hΓ
  obtain ⟨u1, hu1⟩ := hnatT (VExpr.nat :: Γ) ⟨hΓ, _, hu0⟩
  obtain rfl | rfl := hi
  · -- `fun _ a => a`
    have hbody : env.HasType U (VExpr.nat :: Γ) (.lam .nat (.bvar 0)) (.forallE .nat .nat) :=
      .lam hu1 (.bvar .zero)
    have hβ1 := VEnv.IsDefEq.beta hbody htT
    have hβ2 := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ)
      (e := .bvar 0) (A := .nat) (B := .nat) (.bvar .zero) heT
    simp [VExpr.inst, VExpr.instVar, VExpr.nat] at hβ1 hβ2 ⊢
    exact ⟨_, ((hβ1.appDF heT).trans hβ2)⟩
  · -- `fun a _ => a`
    have hbody : env.HasType U (VExpr.nat :: Γ) (.lam .nat (.bvar 1)) (.forallE .nat .nat) :=
      .lam hu1 (.bvar (.succ .zero))
    have hβ1 := VEnv.IsDefEq.beta hbody htT
    have hβ2 := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ)
      (e := t.lift) (A := .nat) (B := .nat)
      (htT.weakN henv (.zero [VExpr.nat] rfl)) heT
    simp [VExpr.inst, VExpr.instVar, VExpr.nat, VExpr.inst_lift] at hβ1 hβ2 ⊢
    exact ⟨_, ((hβ1.appDF heT).trans hβ2)⟩

/-- The shape of `Reflection.ite`'s translation: four lambdas over `ite` at the reflection's own
decision. Everything `checkITE` says is about applications of this term, so this is where the
`VExpr` it denotes is pinned down -- including that the `type` and `toDec` occurring under its
binders are the very ones `Reflection.WF` names, which is `of_nil_unique`'s job. -/
theorem Reflection.ite_tr {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (hnil : c.vlctx = []) (htypeOK : CondOK r.type) (htoDecOK : CondOK r.toDec)
    {toDec' : VExpr} (htoDec : c.TrExprS r.toDec toDec')
    {ite₀ : VExpr} (H : TrExprS c.venv c.lparams [] r.ite ite₀) :
    ite₀ = VExpr.lams
      [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0), .sort (.succ .zero)]
      (((vexpr(@_root_.ite.{1}).app (.bvar 0)).app (.bvar 3)).app
        (((toDec'.app (.bvar 3)).app (.bvar 2)).app (.bvar 1))) := by
  have hty0 : c.venv.contains ``Nat → True := fun _ => trivial
  have htypeTr : ∀ {Δ : VLCtx} {x}, TrExprS c.venv c.lparams Δ r.type x → x = w.type' :=
    fun h => TrExprS.of_nil_unique c.Ewf.ordered
      (CondOK.noProj htypeOK)
      (by rw [← hnil]; exact w.htype) h
  have htoDecTr : ∀ {Δ : VLCtx} {x}, TrExprS c.venv c.lparams Δ r.toDec x → x = toDec' :=
    fun h => TrExprS.of_nil_unique c.Ewf.ordered
      (CondOK.noProj htoDecOK) (by rw [← hnil]; exact htoDec) h
  unfold Reflection.ite at H
  simp only [Expr.lam0, mkApp3, mkApp2, mkApp] at H
  -- peel the four binders, then the application spine of the body
  cases H with | lam _ hd1 H
  cases hd1 with | sort h1
  cases H with | lam _ hd2 H
  obtain ⟨rfl, -⟩ := hd2.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  cases H with | lam _ hd3 H
  cases hd3 with | app _ _ hd3f hd3a
  cases hd3f with | app _ _ hd3ff hd3fa
  cases hd3fa with | bvar hb1
  cases hd3a with | bvar hb0
  cases H with | lam _ hd4 H
  cases hd4 with | sort h4
  cases H with | app _ _ hbf hba
  cases hbf with | app _ _ hbff hbfa
  cases hbff with | app _ _ hbfff hbffa
  cases hbfff with | const hc hus hlen
  cases hbffa with | bvar hbb0
  cases hbfa with | bvar hbb3
  cases hba with | app _ _ hta htb
  cases hta with | app _ _ htaa htab
  cases htaa with | app _ _ htd htdb
  cases htdb with | bvar hd3'
  cases htab with | bvar hd2'
  cases htb with | bvar hd1'
  simp only [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, Option.some.injEq, Prod.mk.injEq] at hb1 hb0 hbb0 hbb3 hd3' hd2' hd1'
  simp [VLevel.ofLevel] at h1 h4
  subst h1; subst h4
  simp at hus
  obtain ⟨u, hu, rfl⟩ := hus
  simp [VLevel.ofLevel] at hu
  subst hu
  obtain ⟨rfl, -⟩ := hb1; obtain ⟨rfl, -⟩ := hb0
  obtain ⟨rfl, -⟩ := hbb0; obtain ⟨rfl, -⟩ := hbb3
  obtain ⟨rfl, -⟩ := hd3'; obtain ⟨rfl, -⟩ := hd2'; obtain ⟨rfl, -⟩ := hd1'
  rw [htypeTr hd3ff, htoDecTr htd]
  simp [VExpr.lams, VExpr.bool, VExpr.liftN, liftVar]

/-- `fun α : Type => fun a _ : α => a` and `fun α : Type => fun _ a : α => a`, the two branches
`checkITE` compares the conditional against. -/
theorem TrExprS.polyProj {env : VEnv} {Us : List Name} {Δ : VLCtx} {n₁ n₂ n₃ bi₁ bi₂ bi₃}
    {i : Nat} (hi : i = 0 ∨ i = 1) :
    TrExprS env Us Δ
      (.lam n₁ q(Type) (.lam n₂ (.bvar 0) (.lam n₃ (.bvar 1) (.bvar i) bi₃) bi₂) bi₁)
      (.lam vexpr(Type) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar i)))) ∧
    env.HasType Us.length Δ.toCtx
      (.lam vexpr(Type) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar i))))
      (.forallE vexpr(Type) (.forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2)))) := by
  have hbody : TrExprS env Us
      ((none, .vlam (.bvar 1)) :: (none, .vlam (.bvar 0)) ::
        (none, .vlam vexpr(Type)) :: Δ) (.bvar i) (.bvar i) ∧
      env.HasType Us.length
        (VExpr.bvar 1 :: VExpr.bvar 0 :: VExpr.sort (.succ .zero) :: Δ.toCtx)
        (.bvar i) (.bvar 2) := by
    obtain rfl | rfl := hi
    · exact ⟨.bvar0, .bvar .zero⟩
    · exact ⟨.bvar1, .bvar (.succ .zero)⟩
  exact ⟨.lam ⟨_, .sort trivial⟩ (.sort rfl)
      (.lam ⟨_, .bvar .zero⟩ .bvar0 (.lam ⟨_, .bvar (.succ .zero)⟩ .bvar1 hbody.1)),
    .lam (.sort trivial) (.lam (.bvar .zero) (.lam (.bvar (.succ .zero)) hbody.2))⟩

/-- The two projections applied to a type and both branches pick one. `checkITE` compares the
conditional against a projection, and the caller's branches are what it is then applied to. -/
theorem VEnv.IsDefEqU.polyProj {env : VEnv} {U Γ} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {α t e : VExpr}
    (hα : env.HasType U Γ α vexpr(Type))
    (htT : env.HasType U Γ t α) (heT : env.HasType U Γ e α) {i : Nat} (hi : i = 0 ∨ i = 1) :
    env.IsDefEqU U Γ
      ((((VExpr.lam vexpr(Type) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar i)))).app α).app t).app e)
      (if i = 1 then t else e) := by
  have hΓ1 : OnCtx (VExpr.sort (.succ .zero) :: Γ) (env.IsType U) := ⟨hΓ, _, .sort trivial⟩
  have hΓ2 : OnCtx (VExpr.bvar 0 :: VExpr.sort (.succ .zero) :: Γ) (env.IsType U) :=
    ⟨hΓ1, _, .bvar .zero⟩
  have hΓ3 : OnCtx (VExpr.bvar 1 :: VExpr.bvar 0 :: VExpr.sort (.succ .zero) :: Γ)
      (env.IsType U) := ⟨hΓ2, _, .bvar (.succ .zero)⟩
  have hbodyT : VExpr.WF env U (VExpr.bvar 1 :: VExpr.bvar 0 :: VExpr.sort (.succ .zero) :: Γ)
      (.bvar i) := by
    obtain rfl | rfl := hi
    · exact ⟨_, .bvar .zero⟩
    · exact ⟨_, .bvar (.succ .zero)⟩
  have hargs : VExpr.ArgsTyped env U Γ
      [.sort (.succ .zero), .bvar 0, .bvar 1] .id [α, t, e] :=
    .cons (by simpa using hα)
      (.cons (by simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id] using htT)
        (.cons (by simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id] using heT) .nil))
  have heq := VExpr.lams_appN' henv hΓ (by simpa using hΓ3) (.id henv hΓ) hargs hbodyT |>.2
  simp only [VExpr.subst_id, VExpr.lams, VExpr.appN] at heq
  refine heq.trans henv hΓ ?_
  obtain rfl | rfl := hi
  · exact ⟨_, heT⟩
  · exact ⟨_, htT⟩

/-- `Prop → Bool → type p b → ∀ α : Type, α → α → α`, the type `checkITE` checks the conditional
against. The third domain is where the reflection's own relation enters, and `of_nil_any` is what
puts the `type'` of `Reflection.WF` there rather than some other translation of `r.type`. -/
theorem TrExprS.reflIteType (w : Reflection.WF c r)
    (hnil : c.vlctx = []) (hbool : c.venv.contains ``Bool) (htypeOK : CondOK r.type)
    (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length)) :
    TrExprS c.venv c.lparams Δ
      (.arrow q(Prop) (.arrow q(Bool)
        (.arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
          (.forallE n₁ q(Type)
            (.forallE n₂ (.bvar 0) (.forallE n₃ (.bvar 1) (.bvar 2) bi₃) bi₂) bi₁))))
      (.forallE vexpr(Prop) (.forallE .bool
        (.forallE ((w.type'.app (.bvar 1)).app (.bvar 0))
          (.forallE vexpr(Type) (.forallE (.bvar 0) (.forallE (.bvar 1) (.bvar 2))))))) := by
  have htypeT : c.venv.HasType c.lparams.length [] w.type' vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [hnil] at h; exact h
  have hΔ1 : OnCtx (.sort .zero :: Δ.toCtx) (c.venv.IsType c.lparams.length) :=
    ⟨hΔ, _, .sort trivial⟩
  have hΔ2 : OnCtx (.bool :: .sort .zero :: Δ.toCtx)
      (c.venv.IsType c.lparams.length) :=
    ⟨hΔ1, c.hasPrimitives.boolIsType' c.Ewf hbool hΔ1⟩
  -- the reflection at the two binders
  have hpT : c.venv.HasType c.lparams.length (.bool :: .sort .zero :: Δ.toCtx)
      (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have hbT : c.venv.HasType c.lparams.length (.bool :: .sort .zero :: Δ.toCtx)
      (.bvar 0) .bool := .bvar .zero
  have htw := htypeT.weak0 (Γ := .bool :: .sort .zero :: Δ.toCtx) c.Ewf
  have hrel : c.venv.HasType c.lparams.length (.bool :: .sort .zero :: Δ.toCtx)
      ((w.type'.app (.bvar 1)).app (.bvar 0)) (.sort .zero) := .app (.app htw hpT) hbT
  have htypeTr : TrExprS c.venv c.lparams
      ((none, .vlam .bool) :: (none, .vlam (.sort .zero)) :: Δ) r.type w.type' :=
    TrExprS.of_nil_any c.Ewf (CondOK.noProj htypeOK) (by rw [← hnil]; exact w.htype)
  exact (TrTy.forallE (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)
    (TrTy.forallE (.of (c.hasPrimitives.trBool c.Ewf hbool) hΔ2.2)
      (TrTy.forallE (.of (.app (.app htw hpT) hbT (.app htw hpT htypeTr .bvar1) .bvar0)
          ⟨_, hrel⟩)
        TrTy.polyIteType))).trS

/-- `Prop → Prop`, the type `checkNatDITE` checks `Not` against. -/
theorem TrExprS.propProp {env : VEnv} {Us : List Name} {Δ : VLCtx} {n bi} :
    TrExprS env Us Δ (.forallE n q(Prop) q(Prop) bi) vexpr(Prop → Prop) :=
  (TrTy.forallE (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)
    (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)).trS

/-- `∀ p : Prop, type p b → C`, the shape of the types `checkNatDITE` checks `ofTrue` and
`ofFalse` against; `C` is the proposition itself for `ofTrue` and its negation for `ofFalse`, so
it is taken as a parameter with its translation. -/
theorem TrExprS.reflOfType (w : Reflection.WF c r)
    (hnil : c.vlctx = []) (hbool : c.venv.contains ``Bool) (htypeOK : CondOK r.type)
    {Δ : VLCtx} (b : Bool)
    (hcod : TrExprS c.venv c.lparams
      ((none, .vlam ((w.type'.app (.bvar 0)).app (.boolLit b))) ::
        (none, .vlam vexpr(Prop)) :: Δ) cod cod')
    (hcodT : c.venv.HasType c.lparams.length
      ((w.type'.app (.bvar 0)).app (.boolLit b) :: .sort .zero :: Δ.toCtx)
      cod' vexpr(Prop)) :
    TrExprS c.venv c.lparams Δ
      (.forallE n₁ q(Prop) (.forallE n₂ (mkApp2 r.type (.bvar 0) (toExpr b)) cod bi₂) bi₁)
      (.forallE vexpr(Prop) (.forallE ((w.type'.app (.bvar 0)).app (.boolLit b)) cod')) := by
  have htypeT : c.venv.HasType c.lparams.length [] w.type' vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [hnil] at h; exact h
  have hrel : c.venv.HasType c.lparams.length (vexpr(Prop) :: Δ.toCtx)
      ((w.type'.app (.bvar 0)).app (.boolLit b)) vexpr(Prop) :=
    .app (.app (VEnv.HasType.weak0 c.Ewf htypeT) (.bvar .zero))
      (VEnv.HasType.weak0 c.Ewf.ordered
        (TrExprS.boolLit (Us := c.lparams) (Δ := []) c.hasPrimitives hbool b).2)
  have htypeTr : TrExprS c.venv c.lparams ((none, .vlam vexpr(Prop)) :: Δ) r.type w.type' :=
    TrExprS.of_nil_any c.Ewf (CondOK.noProj htypeOK) (by rw [← hnil]; exact w.htype)
  exact (TrTy.forallE (.of (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩)
    (TrTy.forallE
      (.of (.app (.app (.weak0 c.Ewf htypeT) (.bvar .zero))
        (.weak0 c.Ewf.ordered
          (TrExprS.boolLit (Us := c.lparams) (Δ := []) c.hasPrimitives hbool b).2)
        (.app (.weak0 c.Ewf htypeT) (.bvar .zero) htypeTr .bvar0)
        (TrExprS.boolLit c.hasPrimitives hbool b).1) ⟨_, hrel⟩)
      (.of hcod ⟨_, hcodT⟩))).trS

/-- `Prop → Bool → type p b → (p → Nat) → (¬p → Nat) → Nat`, the type `checkNatDITE` checks the
`dite` gadget against. `Not` enters as a parameter: the check before it is what establishes that
the constant is a `Prop → Prop`, and nothing else about it is known. -/
theorem TrExprS.reflDiteType (w : Reflection.WF c r)
    (hnil : c.vlctx = []) (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (htypeOK : CondOK r.type)
    {Not' : VExpr} (hNotTr : ∀ {Δ}, TrExprS c.venv c.lparams Δ (.const ``Not []) Not')
    (hNotT : ∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ Not' vexpr(Prop → Prop))
    (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length)) :
    TrExprS c.venv c.lparams Δ
      (.forallE n₁ (.sort .zero) (.forallE n₂ (.const ``Bool [])
        (.forallE n₃ (mkApp2 r.type (.bvar 1) (.bvar 0))
          (.forallE n₄ (.forallE n₆ (.bvar 2) (.const ``Nat []) bi₆)
            (.forallE n₅ (.forallE n₇ (mkApp (.const ``Not []) (.bvar 3)) (.const ``Nat []) bi₇)
              (.const ``Nat []) bi₅) bi₄) bi₃) bi₂) bi₁)
      (.forallE (.sort .zero) (.forallE .bool
        (.forallE ((w.type'.app (.bvar 1)).app (.bvar 0))
          (.forallE (.forallE (.bvar 2) .nat)
            (.forallE (.forallE (Not'.app (.bvar 3)) .nat) .nat))))) := by
  have htypeT : c.venv.HasType .. := w.typeT; rw [hnil] at htypeT
  have htw {Γ} : c.venv.HasType _ Γ .. := .weak0 c.Ewf htypeT
  have htypeTr : ∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ r.type w.type' := fun {_} =>
    TrExprS.of_nil_any c.Ewf.ordered
      (CondOK.noProj htypeOK)
      (by rw [← hnil]; exact w.htype)
  have hnatT {Γ : List VExpr} (h : OnCtx Γ (c.venv.IsType c.lparams.length)) :
      c.venv.IsType c.lparams.length Γ VExpr.nat := c.hasPrimitives.natIsType' c.Ewf hnat h
  have hΔ1 : OnCtx (.sort .zero :: Δ.toCtx) (c.venv.IsType c.lparams.length) :=
    ⟨hΔ, _, .sort trivial⟩
  have hΔ2 : OnCtx (.bool :: _) (c.venv.IsType c.lparams.length) :=
    ⟨hΔ1, c.hasPrimitives.boolIsType' c.Ewf hbool hΔ1⟩
  have hrel : c.venv.HasType c.lparams.length (.bool :: .sort .zero :: Δ.toCtx)
      ((w.type'.app (.bvar 1)).app (.bvar 0)) vexpr(Prop) :=
    .app (.app htw (.bvar (.succ .zero))) (.bvar .zero)
  have hΔ3 : OnCtx (_ :: .bool :: _) (c.venv.IsType c.lparams.length) := ⟨hΔ2, _, hrel⟩
  have hpT : c.venv.HasType c.lparams.length
      ((w.type'.app (.bvar 1)).app (.bvar 0) :: .bool :: .sort .zero :: Δ.toCtx)
      (.bvar 2) vexpr(Prop) := .bvar (.succ (.succ .zero))
  have hΔ4 : OnCtx (.bvar 2 :: _) (c.venv.IsType c.lparams.length) := ⟨hΔ3, _, hpT⟩
  -- the branch types, `p → Nat` and `¬p → Nat`, as `TrTy`s so their `IsType`s are available
  let T4 : TrTy c.venv c.lparams
      ((none, .vlam ((w.type'.app (.bvar 1)).app (.bvar 0))) :: (none, .vlam .bool) ::
        (none, .vlam vexpr(Prop)) :: Δ)
      (.forallE n₆ (.bvar 2) (.const ``Nat []) bi₆) :=
    TrTy.forallE (.of .bvar2 ⟨_, hpT⟩)
      (.of (c.hasPrimitives.trNat c.Ewf hnat) (hnatT hΔ4))
  have hΔ5 : OnCtx (T4.tgt :: _) (c.venv.IsType c.lparams.length) := ⟨hΔ3, T4.isType⟩
  have hnotT : c.venv.HasType c.lparams.length
      (T4.tgt :: (w.type'.app (.bvar 1)).app (.bvar 0) :: .bool :: .sort .zero :: Δ.toCtx)
      (Not'.app (.bvar 3)) vexpr(Prop) := .app hNotT (.bvar (.succ (.succ (.succ .zero))))
  have hΔ6 : OnCtx (Not'.app (.bvar 3) :: _) (c.venv.IsType c.lparams.length) :=
    ⟨hΔ5, _, hnotT⟩
  let T5 : TrTy c.venv c.lparams
      ((none, .vlam T4.tgt) :: (none, .vlam ((w.type'.app (.bvar 1)).app (.bvar 0))) ::
        (none, .vlam .bool) :: (none, .vlam vexpr(Prop)) :: Δ)
      (.forallE n₇ (mkApp q(Not) (.bvar 3)) q(Nat) bi₇) :=
    TrTy.forallE (.of (.app hNotT (.bvar (.succ (.succ (.succ .zero)))) hNotTr .bvar3)
        ⟨_, hnotT⟩)
      (.of (c.hasPrimitives.trNat c.Ewf hnat) (hnatT hΔ6))
  have hΔ7 : OnCtx (T5.tgt :: _) (c.venv.IsType c.lparams.length) := ⟨hΔ5, T5.isType⟩
  exact (TrTy.forallE
    (.of (TrExprS.sort (u := .zero) (u' := .zero) rfl) ⟨_, .sort (l := .zero) trivial⟩)
    (TrTy.forallE (.of (c.hasPrimitives.trBool c.Ewf hbool) hΔ2.2)
      (TrTy.forallE
        (.of (.app (.app htw (.bvar (.succ .zero))) (.bvar .zero)
            (.app htw (.bvar (.succ .zero)) htypeTr .bvar1) .bvar0) ⟨_, hrel⟩)
        (TrTy.forallE T4 (TrTy.forallE T5
          (.of (c.hasPrimitives.trNat c.Ewf hnat) (hnatT hΔ7))))))).trS

/-- The shape of `Reflection.natDITE`'s translation: three lambdas over `dite` at `Nat` and the
reflection's own decision. The `checkITE` counterpart is `ite_tr`. -/
theorem Reflection.natDITE_tr {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (hnil : c.vlctx = []) (htypeOK : CondOK r.type) (htoDecOK : CondOK r.toDec)
    {toDec' : VExpr} (htoDec : c.TrExprS r.toDec toDec')
    {d₀ : VExpr} (H : TrExprS c.venv c.lparams [] r.natDITE d₀) :
    d₀ = VExpr.lams [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0)]
      ((vexpr(@dite.{1} Nat).app (.bvar 2)).app
        (((toDec'.app (.bvar 2)).app (.bvar 1)).app (.bvar 0))) := by
  have htypeTr {Δ x} (h : TrExprS c.venv c.lparams Δ r.type x) : x = w.type' :=
    TrExprS.of_nil_unique c.Ewf (CondOK.noProj htypeOK) (by rw [← hnil]; exact w.htype) h
  have htoDecTr {Δ x} (h : TrExprS c.venv c.lparams Δ r.toDec x) : x = toDec' :=
    TrExprS.of_nil_unique c.Ewf (CondOK.noProj htoDecOK) (by rw [← hnil]; exact htoDec) h
  unfold Reflection.natDITE at H
  simp only [Expr.lam0, mkApp3, mkApp2, mkApp] at H
  cases H with | lam _ hd1 H
  cases hd1 with | sort h1
  cases H with | lam _ hd2 H
  obtain ⟨rfl, -⟩ := hd2.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  cases H with | lam _ hd3 H
  cases hd3 with | app _ _ hd3f hd3a
  cases hd3f with | app _ _ hd3ff hd3fa
  cases hd3fa with | bvar hb1
  cases hd3a with | bvar hb0
  cases H with | app _ _ hbf hba
  cases hbf with | app _ _ hbff hbfa
  cases hbff with | app _ _ hbfff hbffa
  cases hbfff with | const hc hus hlen
  obtain ⟨rfl, -⟩ := hbffa.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  cases hbfa with | bvar hbb2
  cases hba with | app _ _ hta htb
  cases hta with | app _ _ htaa htab
  cases htaa with | app _ _ htd htdb
  cases htdb with | bvar hd2'
  cases htab with | bvar hd1'
  cases htb with | bvar hd0'
  simp only [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, Option.some.injEq, Prod.mk.injEq] at hb1 hb0 hbb2 hd2' hd1' hd0'
  simp [VLevel.ofLevel] at h1
  subst h1
  simp at hus
  obtain ⟨u, hu, rfl⟩ := hus
  simp [VLevel.ofLevel] at hu
  subst hu
  obtain ⟨rfl, -⟩ := hb1; obtain ⟨rfl, -⟩ := hb0; obtain ⟨rfl, -⟩ := hbb2
  obtain ⟨rfl, -⟩ := hd2'; obtain ⟨rfl, -⟩ := hd1'; obtain ⟨rfl, -⟩ := hd0'
  rw [htypeTr hd3ff, htoDecTr htd]
  simp [VExpr.lams, VExpr.bool, VExpr.liftN, liftVar]

/-- An equation the checker verified under a telescope of binders, at arbitrary arguments for
them in an arbitrary context. Every binder the reflection's checks open has a closed type, which
is what lets the equation weaken past the caller's context untouched; the closing is then the
substitution the arguments define. -/
theorem Reflection.WF.genTele {c : VContext} (E : c.Ext)
    (hAs : OnCtx As.reverse (c.venv.IsType c.lparams.length))
    (hXY : c.venv.IsDefEqU c.lparams.length As.reverse X Y)
    (hXc : X.ClosedN As.length) (hYc : Y.ClosedN As.length)
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hargs : VExpr.ArgsTyped E.venv c.lparams.length Γ As .id vs) :
    E.venv.IsDefEqU c.lparams.length Γ (X.subst (VExpr.Subst.id.consN vs))
      (Y.subst (VExpr.Subst.id.consN vs)) := by
  have hAs := E.monoCtx hAs
  have hW : Ctx.LiftN Γ.length As.length As.reverse (As.reverse ++ Γ) := by
    simpa using Ctx.LiftN.right (VEnv.CtxWF.closed E.wf hAs) Γ
  have hXY' := (E.mono hXY).weakN E.wf hW
  rw [hXc.liftN_eq (Nat.le_refl _), hYc.liftN_eq (Nat.le_refl _)] at hXY'
  exact hXY'.subst E.wf
    (VExpr.ArgsTyped.substEq (OnCtx.append_right E.wf hAs hΓ) (.id E.wf hΓ) hargs)

/-- `genTele` for a typing rather than an equation: the type travels with the term, which is what
a caller needs of the gadget's pieces -- that `prop x y` is a proposition and `proof x y` is
evidence about *that* proposition, at the caller's own `x` and `y`. Everything in sight is
closed, so the type is substituted along with the term and the two stay in step. -/
theorem Reflection.WF.genTeleT {c : VContext} (E : c.Ext)
    (hAs : OnCtx As.reverse (c.venv.IsType c.lparams.length))
    (hX : c.venv.HasType c.lparams.length As.reverse X A)
    (hXc : X.ClosedN As.length) (hAc : A.ClosedN As.length)
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hargs : VExpr.ArgsTyped E.venv c.lparams.length Γ As .id vs) :
    E.venv.HasType c.lparams.length Γ (X.subst (VExpr.Subst.id.consN vs))
      (A.subst (VExpr.Subst.id.consN vs)) := by
  have hAs := E.monoCtx hAs
  have hW : Ctx.LiftN Γ.length As.length As.reverse (As.reverse ++ Γ) := by
    simpa using Ctx.LiftN.right (VEnv.CtxWF.closed E.wf hAs) Γ
  have hX' := VEnv.HasType.weakN E.wf hW (E.monoT hX)
  rw [hXc.liftN_eq (Nat.le_refl _), hAc.liftN_eq (Nat.le_refl _)] at hX'
  exact hX'.subst E.wf.orderedStrong
    (VExpr.ArgsTyped.substEq (OnCtx.append_right E.wf hAs hΓ) (.id E.wf hΓ) hargs)

/-- An equation the checker verified under `p : Prop` and `H : type p b`, moved to arbitrary such
arguments in an arbitrary context. Two steps: the checked equation lives at the two-binder context
over `[]`, so it weakens past whatever the caller has built (everything in sight is closed, so the
lift is the identity), and then the two binders are closed off by a substitution whose typing
obligations are exactly the caller's hypotheses. -/
theorem Reflection.WF.genPH (w : Reflection.WF c r) (E : c.Ext)
    (hnil : c.vlctx = []) (hbool : c.venv.contains ``Bool) (b : Bool) {X Y : VExpr}
    (hXY : c.venv.IsDefEqU c.lparams.length
      [(w.type'.app (.bvar 0)).app (.boolLit b), vexpr(Prop)] X Y)
    (hXc : X.ClosedN 2) (hYc : Y.ClosedN 2)
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hp : E.venv.HasType c.lparams.length Γ p vexpr(Prop))
    (hH : E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app (.boolLit b))) :
    E.venv.IsDefEqU c.lparams.length Γ (X.subst ((VExpr.Subst.id.cons p).cons H))
      (Y.subst ((VExpr.Subst.id.cons p).cons H)) := by
  have htypeT : c.venv.HasType c.lparams.length [] w.type'
      vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [hnil] at h; exact h
  have hclosed : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
  have hbc : (VExpr.boolLit b).ClosedN := by cases b <;> trivial
  have hblit : ∀ Γ', E.venv.HasType c.lparams.length Γ' (VExpr.boolLit b) .bool := fun Γ' =>
    VEnv.HasType.weak0 E.wf <| E.monoT
      (TrExprS.boolLit (Us := c.lparams) (Δ := []) c.hasPrimitives hbool b).2
  -- the binder types, in the caller's context
  have hPT : E.venv.HasType c.lparams.length Γ vexpr(Prop) vexpr(Type) :=
    .sort trivial
  have hHT : E.venv.HasType c.lparams.length (vexpr(Prop) :: Γ)
      ((w.type'.app (.bvar 0)).app (.boolLit b)) vexpr(Prop) :=
    .app (.app (VEnv.HasType.weak0 E.wf (E.monoT htypeT)) (.bvar .zero)) (hblit _)
  -- weaken the checked equation past the caller's context
  have hW : Ctx.LiftN Γ.length 2 [(w.type'.app (.bvar 0)).app (.boolLit b), vexpr(Prop)]
      ((w.type'.app (.bvar 0)).app (.boolLit b) :: vexpr(Prop) :: Γ) := by
    have h0 : Ctx.LiftN Γ.length 0 [] Γ := by simpa using Ctx.LiftN.zero (Γ := []) Γ
    have h2 := (h0.succ (A := vexpr(Prop))).succ (A := (w.type'.app (.bvar 0)).app (.boolLit b))
    simpa [VExpr.liftN, liftVar, hclosed.liftN_eq (Nat.zero_le _),
      hbc.liftN_eq (Nat.zero_le _)] using h2
  have hXY' := (E.mono hXY).weakN E.wf hW
  rw [hXc.liftN_eq (Nat.le_refl _), hYc.liftN_eq (Nat.le_refl _)] at hXY'
  -- and close the two binders
  refine hXY'.subst E.wf.orderedStrong
    (VEnv.Ctx.SubstEq.cons (VEnv.Ctx.SubstEq.cons (.id E.wf hΓ) hPT ?_) hHT ?_) hΓ
  · exact hp
  · show E.venv.HasType _ _ _ _
    rw [VExpr.Subst.tail_cons,
      show ((w.type'.app (VExpr.bvar 0)).app (VExpr.boolLit b)).subst
        (VExpr.Subst.id.cons p) = (w.type'.app p).app (VExpr.boolLit b) from by
      simp [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, hclosed.subst_eq', hbc.subst_eq']]
    exact hH

/-- What one of `checkITE`'s two equation checks says, generalized away from the binders it was
checked under: at *any* proposition and evidence for the literal `b`, the conditional is the
matching projection. `genPH` is what produces it. -/
def Reflection.WF.IteEq (w : Reflection.WF c r) (ite₀ : VExpr) (b : Bool) : Prop :=
  ∀ (E : c.Ext) {Γ : List VExpr} {p H : VExpr}, OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p vexpr(Prop) →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app (.boolLit b)) →
    E.venv.IsDefEqU c.lparams.length Γ (((ite₀.app p).app (.boolLit b)).app H)
      (.lam vexpr(Type) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar (if b then 1 else 0)))))

theorem Reflection.check.WF {c : VContext} {s : VState} {r : Reflection} {fail : ∀ {α}, M α}
    (hbool : c.venv.contains ``Bool) (hnil : c.vlctx = []) (htypeOK : CondOK r.type)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (r.check fail).WF c s fun _ _ => Nonempty (Reflection.WF c r) := by
  have hfailb : ∀ {α β} {k : α → M β} {c s Q}, (fail >>= k).WF c s Q :=
    .bind (hfail (Q := fun _ _ => False)) fun _ _ _ h => h.elim
  have hnil' : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  unfold Reflection.check
  -- `type : Prop → Bool → Prop`
  refine .bind (checkType.WF (CondOK.fvarsIn htypeOK))
    fun _ _ _ ⟨type', typeTy', _, htypeTr, htypeTyTr, htypeT⟩ => ?_
  refine .bind (isDefEq.WF htypeTyTr
    (TrExprS.propBoolProp c.Ewf c.hasPrimitives hbool c.Δwf.toCtx)) fun _ _ _ hpb => ?_
  split <;> [rename_i h1; exact hfail]
  have htypeT' : c.venv.HasType c.lparams.length c.vlctx.toCtx type'
      vexpr(Prop → Bool → Prop) :=
    VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hpb h1) htypeT
  have htypeTΓ : ∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ type'
      vexpr(Prop → Bool → Prop) := fun {_} =>
    VEnv.HasType.weak0 c.Ewf (by rw [← hnil']; exact htypeT')
  have htypeTrΓ : ∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ r.type type' := fun {_} =>
    TrExprS.of_nil_any c.Ewf.ordered
      (CondOK.noProj htypeOK)
      (by rw [← hnil]; exact htypeTr)
  exact .pure ⟨{ type' := type', htype := htypeTr, typeT := htypeT' }⟩

/-- `c` and `c.withMLC c.mlctx` are the same context, but not by `rfl`, and rewriting the goal
fails whenever its postcondition mentions `c`. Converting the whole judgement sidesteps that. -/
theorem M.WF.withMLC_self {α} {c : VContext} {s : VState} {x : M α} {Q : α → VState → Prop}
    (h : M.WF (c.withMLC c.mlctx) s x Q) : M.WF c s x Q := c.withMLC_self ▸ h

/-- That the conditional the reflection builds is *well typed* at any proposition, boolean and
evidence -- not only at a decided boolean, which is all `WF_ite` speaks about. A consumer needs
this to build the conditional at all: nothing else in the model types an `ite` application, since
`ite`'s own declared type is not checked anywhere. -/
def Reflection.WF.ITE_T {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (toDec' : VExpr) : Prop :=
  ∀ (E : c.Ext) {Γ : List VExpr} {p H bb α : VExpr},
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p vexpr(Prop) →
    E.venv.HasType c.lparams.length Γ bb .bool →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app bb) →
    E.venv.HasType c.lparams.length Γ α vexpr(Type) →
    E.venv.HasType c.lparams.length Γ
      (((vexpr(@_root_.ite.{1}).app α).app p).app
        (((toDec'.app p).app bb).app H))
      (.forallE α (.forallE α.lift α.lift.lift))

/-- The `ite` gadget's well-typedness is what types `toDec`: the decision sits in the gadget's
instance position, so peeling the application back off is the whole proof. The type argument is
`Prop`; any closed type would do, and this one needs nothing from the environment. -/
theorem Reflection.WF.ITE_T.toDecT {c : VContext} {r : Reflection} {w : Reflection.WF c r}
    {toDec' : VExpr} (h : w.ITE_T toDec') : w.ToDecT toDec' := by
  intro E Γ p bb H hΓ hp hbb hH
  obtain ⟨_, _, -, ha⟩ := VExpr.WF.app_inv E.wf hΓ
    ⟨_, h E hΓ hp hbb hH (α := vexpr(Prop)) (.sort trivial)⟩
  exact ⟨_, ha⟩

/-- Verification boundary for `Reflection.checkITE`: at evidence for either literal, the
conditional the reflection builds *is* the corresponding projection, at every proposition and in
every context. The checker verifies this once, under its own `p` and `H` binders; `genPH` moves
it, and `ite_tr` is what makes the term it moves recognizable as `iteApp`. -/
theorem Reflection.checkITE.WF {fail : ∀ {α}, M α}
    (w : Reflection.WF c r) (hnil : c.vlctx = []) (hbool : c.venv.contains ``Bool)
    {toDec' : VExpr} (htoDec : c.TrExprS r.toDec toDec') (htoDecC : toDec'.ClosedN)
    (htypeOK : CondOK r.type) (htoDecOK : CondOK r.toDec) (hiteOK : CondOK r.ite)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (r.checkITE fail).WF c s fun _ _ => w.WF_ite toDec' ∧ w.ITE_T toDec' := by
  have hfailb : ∀ {α β} {k : α → M β} {c s Q}, (fail >>= k).WF c s Q :=
    .bind (hfail (Q := fun _ _ => False)) fun _ _ _ h => h.elim
  have hnil' : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  have htypeT : c.venv.HasType c.lparams.length [] w.type' vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [hnil'] at h; exact h
  unfold Reflection.checkITE
  refine .bind (checkType.WF (CondOK.fvarsIn hiteOK))
    fun _ _ _ ⟨ite₀, iteTy', _, hiteTr, hiteTyTr, hiteT⟩ => ?_
  refine .bind (isDefEq.WF hiteTyTr (TrExprS.reflIteType w hnil hbool htypeOK c.Δwf.toCtx))
    fun _ _ _ harr => ?_
  split <;> [rename_i h1; exact hfailb]
  -- the conditional's shape, and its type on the nose
  have hshape := Reflection.ite_tr w hnil htypeOK htoDecOK htoDec (by rw [← hnil]; exact hiteTr)
  have hiteT' := VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (harr h1) hiteT
  rw [hnil'] at hiteT'
  have hiteC := (hiteT'.closedN' c.Ewf.ordered.closed trivial).1
  -- the `p` binder
  refine M.WF.withMLC_self ?_
  simp only []
  refine M.WF.withLocalDecl (m := c.mlctx) (ty := q(Prop)) (ty' := vexpr(Prop))
    (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩ .rfl ?_
  intro idp cwfp s2 hs2 hres2
  -- the `H` binder's type, at either literal
  have hpvT : (c.withMLC _ (wf := cwfp)).HasType (.bvar 0) (.sort .zero) := .bvar .zero
  have hlit {Δ : VLCtx} (b : Bool) : TrExprS c.venv c.lparams Δ (toExpr b) (.boolLit b) ∧
      c.venv.HasType c.lparams.length Δ.toCtx (.boolLit b) .bool :=
    TrExprS.boolLit c.hasPrimitives hbool b
  have htypeTrp {Δ : VLCtx} : TrExprS c.venv c.lparams Δ r.type w.type' :=
    TrExprS.of_nil_any c.Ewf (CondOK.noProj htypeOK) (by rw [← hnil]; exact w.htype)
  have htwp {Γ : List VExpr} : c.venv.HasType c.lparams.length Γ w.type'
      vexpr(Prop → Bool → Prop) := .weak0 c.Ewf htypeT
  have hHtyT (b : Bool) : (c.withMLC _ (wf := cwfp)).HasType
      ((w.type'.app (.bvar 0)).app (.boolLit b)) vexpr(Prop) := .app (.app htwp hpvT) (hlit b).2
  have hHtyTr (b : Bool) : (c.withMLC _ (wf := cwfp)).TrExprS
      (mkApp2 r.type (.fvar idp) (toExpr b)) ((w.type'.app (.bvar 0)).app (.boolLit b)) :=
    .app (.app htwp hpvT) (hlit b).2
      (.app htwp hpvT htypeTrp (.fvar VLCtx.find?_vlam_self)) (hlit b).1
  -- one of the two equation blocks
  have block (b : Bool) (idH : FVarId)
      (cwfH : c.MLCWF (.vlam idH `H (mkApp2 r.type (.fvar idp) (toExpr b))
        ((w.type'.app (.bvar 0)).app (.boolLit b)) .default
        (.vlam idp `p q(Prop) vexpr(Prop) .default c.mlctx))) :
      (c.withMLC _ (wf := cwfH)).TrExprS
        (mkApp3 r.ite (.fvar idp) (toExpr b) (.fvar idH))
        (((ite₀.app (.bvar 1)).app (.boolLit b)).app (.bvar 0)) := by
    have hΓH := (c.withMLC _ (wf := cwfH)).Δwf.toCtx
    -- the three arguments, as translations
    have hp0 : (c.withMLC _ (wf := cwfp)).TrExprS (.fvar idp) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    have hp' := hp0.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    have hH' : (c.withMLC _ (wf := cwfH)).TrExprS (.fvar idH) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    have hiteTrH : (c.withMLC _ (wf := cwfH)).TrExprS r.ite _ :=
      TrExprS.of_nil_any c.Ewf.ordered
        (CondOK.noProj hiteOK)
        (by rw [← hnil]; exact hiteTr)
    -- the application is well typed: peel the conditional's three outer binders off its own type
    have hiteT'' := VEnv.HasType.weak0 (Γ := (c.withMLC _ (wf := cwfH)).vlctx.toCtx)
      c.Ewf hiteT'
    rw [hshape] at hiteTrH hiteT'' ⊢
    obtain ⟨hΓ1, hb1⟩ := VExpr.WF.lam_inv' c.Ewf.orderedStrong hΓH ⟨_, hiteT''⟩
    obtain ⟨hΓ2, hb2⟩ := VExpr.WF.lam_inv' c.Ewf hΓ1 hb1
    obtain ⟨hΓ3, hb3⟩ := VExpr.WF.lam_inv' c.Ewf hΓ2 hb2
    have hargs : VExpr.ArgsTyped c.venv c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
        [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0)] .id
        [.bvar 1, .boolLit b, .bvar 0] := by
      refine .cons (by simpa using (.bvar (.succ .zero) :
        c.venv.HasType c.lparams.length _ (VExpr.bvar 1) vexpr(Prop)))
        (.cons (by simpa using (hlit b).2) (.cons ?_ .nil))
      have h : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
          (.bvar 0) (((w.type'.app (.bvar 0)).app (.boolLit b)).lift) := .bvar .zero
      have hc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
      have hbc : (VExpr.boolLit b).ClosedN := by cases b <;> trivial
      simpa [VExpr.lift, VExpr.liftN, liftVar, VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id,
        hc.liftN_eq (Nat.zero_le _), hbc.liftN_eq (Nat.zero_le _),
        hc.subst_eq', hbc.subst_eq'] using h
    have hwf := (VExpr.lams_appN' c.Ewf hΓH (by simpa using hΓ3) (.id c.Ewf hΓH) hargs hb3).1
    simp only [VExpr.subst_id, VExpr.appN] at hwf
    exact TrExprS.appN c.Ewf.orderedStrong hΓH hiteTrH
      (.cons hp' (.cons (hlit b).1 (.cons hH' .nil))) hwf
  -- each check, generalized away from the two binders it was run under
  have hgen (b : Bool) (idH : FVarId)
      (cwfH : c.MLCWF (.vlam idH `H (mkApp2 r.type (.fvar idp) (toExpr b))
        ((w.type'.app (.bvar 0)).app (.boolLit b)) .default
        (.vlam idp `p q(Prop) vexpr(Prop) .default c.mlctx))) :
      (c.withMLC _ (wf := cwfH)).IsDefEqU
        (((ite₀.app (.bvar 1)).app (.boolLit b)).app (.bvar 0))
        (.lam (.sort (.succ .zero))
          (.lam (.bvar 0) (.lam (.bvar 1) (.bvar (if b then 1 else 0))))) →
      w.IteEq ite₀ b := by
    intro heq E Γ p H hΓ hp hH
    have hbc : (VExpr.boolLit b).ClosedN := by cases b <;> trivial
    have heq' : c.venv.IsDefEqU c.lparams.length
        ((w.type'.app (.bvar 0)).app (.boolLit b) :: vexpr(Prop) :: c.vlctx.toCtx) _ _ := heq
    rw [hnil'] at heq'
    have h := w.genPH E hnil hbool b heq'
      (by exact ⟨⟨⟨hiteC.mono (Nat.zero_le _), by simp [VExpr.ClosedN]⟩,
        hbc.mono (Nat.zero_le _)⟩, by simp [VExpr.ClosedN]⟩)
      (by cases b <;> simp [VExpr.ClosedN]) hΓ hp hH
    have hprojC : (VExpr.lam (.sort (.succ .zero))
        (.lam (.bvar 0) (.lam (.bvar 1) (.bvar (if b then 1 else 0))))).ClosedN := by
      cases b <;> simp [VExpr.ClosedN]
    simp only [VExpr.subst_app] at h
    rw [hiteC.subst_eq', hbc.subst_eq', hprojC.subst_eq'] at h
    simpa [VExpr.Subst.cons, VExpr.Subst.id] using h
  -- the two blocks, then the reflection's `ite` equation at every argument
  refine .bind (Q := fun _ _ => w.IteEq ite₀ true) ?_ fun _ _ _ hTrue => ?_
  · refine M.WF.withLocalDecl (hHtyTr true) ⟨_, hHtyT true⟩ .rfl ?_
    intro idH cwfH s3 hs3 hres3
    refine .bind (isDefEq.WF (block true idH cwfH) (TrExprS.polyProj (Or.inr rfl)).1)
      fun _ _ _ heq => ?_
    split <;> [rename_i h2; exact hfail]
    exact .pure (hgen true idH cwfH (heq h2))
  refine M.WF.withLocalDecl (hHtyTr false) ⟨_, hHtyT false⟩ .rfl ?_
  intro idH cwfH s3 hs3 hres3
  refine .bind (isDefEq.WF (block false idH cwfH) (TrExprS.polyProj (Or.inl rfl)).1)
    fun _ _ _ heq => ?_
  split <;> [rename_i h2; exact hfail]
  have hFalse : w.IteEq ite₀ false := hgen false idH cwfH (heq h2)
  refine .pure ⟨?_, ?_⟩
  case refine_2 =>
    -- the conditional is well typed at *any* boolean, which is what a consumer needs to build it
    intro E Γ p H bb α hΓ hp hbb hH hα
    have hiteTΓ := (E.monoT hiteT').weak0 (Γ := Γ) E.wf.ordered
    rw [hshape] at hiteTΓ
    obtain ⟨hΓ1, hb1'⟩ := VExpr.WF.lam_inv' E.wf hΓ ⟨_, hiteTΓ⟩
    obtain ⟨hΓ2, hb2'⟩ := VExpr.WF.lam_inv' E.wf hΓ1 hb1'
    obtain ⟨hΓ3, hb3'⟩ := VExpr.WF.lam_inv' E.wf hΓ2 hb2'
    obtain ⟨hΓ4, hb4'⟩ := VExpr.WF.lam_inv' E.wf hΓ3 hb3'
    have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
    have hargs4 : VExpr.ArgsTyped E.venv c.lparams.length Γ
        [vexpr(Prop), .bool, (w.type'.app (.bvar 1)).app (.bvar 0), vexpr(Type)] .id
        [p, bb, H, α] := by
      refine .cons (by simpa using hp) (.cons (by simpa using hbb) (.cons ?_
        (.cons (by simpa using hα) .nil)))
      simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq'] using hH
    have h4 := VEnv.HasType.appN_forallEs hargs4
      (by simpa using VEnv.HasType.weak0 (Γ := Γ) E.wf (E.monoT hiteT'))
    have hbeta := (VExpr.lams_appN' E.wf hΓ (by simpa using hΓ4) (.id E.wf hΓ) hargs4 hb4').2
    simp only [VExpr.subst_id, VExpr.lams_nil] at hbeta
    rw [← hshape] at hbeta
    have h5 := VEnv.HasType.defeqU_l E.wf hΓ hbeta h4
    simp only [VExpr.subst_app, VExpr.subst_const] at h5
    rw [htoDecC.subst_eq'] at h5
    simpa [VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id, VExpr.subst,
      VExpr.Subst.lift] using h5
  intro E Γ p H α t e b hΓ hp hH hα ht he
  have hIte : w.IteEq ite₀ b := by cases b; exacts [hFalse, hTrue]
  have heqb := hIte E hΓ hp hH
  -- the projection at the caller's type and branches
  have hproj := VEnv.IsDefEqU.polyProj (i := if b then 1 else 0) E.wf hΓ hα ht he
    (by cases b <;> simp)
  have hprojwf : VExpr.WF E.venv c.lparams.length Γ
      (((VExpr.lam vexpr(Type)
        (.lam (.bvar 0) (.lam (.bvar 1) (.bvar (if b then 1 else 0))))).appN [α, t, e])) := by
    obtain ⟨_, h⟩ := hproj; exact ⟨_, h.hasType.1⟩
  -- transport the check's equation to the full application
  have hspine := (heqb.symm.appN E.wf hΓ (vs := [α, t, e]) hprojwf).symm
  refine .trans E.wf hΓ ?_ (.trans E.wf hΓ hspine ?_)
  · -- the conditional, beta-reduced at all four of its binders
    have hiteTΓ := VEnv.HasType.weak0 (Γ := Γ) E.wf (E.monoT hiteT')
    rw [hshape] at hiteTΓ
    obtain ⟨hΓ1, hb1⟩ := VExpr.WF.lam_inv' E.wf hΓ ⟨_, hiteTΓ⟩
    obtain ⟨hΓ2, hb2⟩ := VExpr.WF.lam_inv' E.wf hΓ1 hb1
    obtain ⟨hΓ3, hb3⟩ := VExpr.WF.lam_inv' E.wf hΓ2 hb2
    obtain ⟨hΓ4, hb4⟩ := VExpr.WF.lam_inv' E.wf hΓ3 hb3
    have hbc : (VExpr.boolLit b).ClosedN := by cases b <;> trivial
    have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
    have hargs : VExpr.ArgsTyped E.venv c.lparams.length Γ
        [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0), .sort (.succ .zero)] .id
        [p, .boolLit b, H, α] :=
      .cons (by simpa using hp) <|
      .cons (by simpa using E.monoT (TrExprS.boolLit (Δ := .ofCtx Γ) c.hasPrimitives hbool b).2) <|
      .cons (by simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq', hbc.subst_eq'] using hH) <|
      .cons (by simpa using hα) .nil
    have hbeta := (VExpr.lams_appN' E.wf hΓ (by simpa using hΓ4) (.id E.wf hΓ) hargs hb4).2
    simp only [VExpr.subst_id] at hbeta
    have hwfspine : VExpr.WF E.venv c.lparams.length Γ
        ((((ite₀.app p).app (VExpr.boolLit b)).app H).appN [α, t, e]) := by
      obtain ⟨_, h⟩ := hspine; exact ⟨_, h.hasType.1⟩
    have hstep := (hshape ▸ hbeta).appN E.wf hΓ (vs := [t, e])
      (by simpa [VExpr.appN] using hwfspine)
    refine .trans E.wf hΓ ?_ hstep.symm
    obtain ⟨A, hA⟩ := hstep
    refine ⟨A, ?_⟩
    have h2 := hA.hasType.2
    simp [VExpr.appN, iteApp, VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id,
      htoDecC.subst_eq'] at h2 ⊢
    exact h2
  · simpa [VExpr.appN] using hproj

/-- What one of `checkNatDITE`'s two equation checks says, generalized away from the four binders
it was run under: at any proposition, branches and evidence for the literal `b`, the gadget takes
the matching branch, applied to the proof the corresponding extractor produces. -/
def Reflection.WF.DiteEq {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (d₀ of' : VExpr) (b : Bool) : Prop :=
  ∀ (E : c.Ext) {Γ : List VExpr} {p H t e : VExpr}, OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p (.sort .zero) →
    E.venv.HasType c.lparams.length Γ t (.forallE p .nat) →
    E.venv.HasType c.lparams.length Γ e (.forallE (vexpr(Not).app p) .nat) →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app (.boolLit b)) →
    E.venv.IsDefEqU c.lparams.length Γ (d₀.appN [p, .boolLit b, H, t, e])
      ((if b then t else e).app ((of'.app p).app H))

/-- That the `dite` gadget is *well typed* at any proposition, boolean and evidence -- the
`DITE` counterpart of `ITE_T`, and needed for the same reason. -/
def Reflection.WF.DITE_T {c : VContext} {r : Reflection} (w : Reflection.WF c r)
    (toDec' : VExpr) : Prop :=
  ∀ (E : c.Ext) {Γ : List VExpr} {p H bb : VExpr},
    OnCtx Γ (E.venv.IsType c.lparams.length) →
    E.venv.HasType c.lparams.length Γ p (.sort .zero) →
    E.venv.HasType c.lparams.length Γ bb .bool →
    E.venv.HasType c.lparams.length Γ H ((w.type'.app p).app bb) →
    E.venv.HasType c.lparams.length Γ
      ((((VExpr.const ``dite [.succ .zero]).app .nat).app p).app
        (((toDec'.app p).app bb).app H))
      (.forallE (.forallE p .nat)
        (.forallE (.forallE (vexpr(Not).app p.lift) .nat) .nat))

/-- `ITE_T.toDecT` for the `dite` gadget, which holds the decision in the same position. -/
theorem Reflection.WF.DITE_T.toDecT {c : VContext} {r : Reflection} {w : Reflection.WF c r}
    {toDec' : VExpr} (h : w.DITE_T toDec') : w.ToDecT toDec' := by
  intro E Γ p bb H hΓ hp hbb hH
  obtain ⟨_, _, -, ha⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, h E hΓ hp hbb hH⟩
  exact ⟨_, ha⟩

/-- Verification boundary for `Reflection.checkNatDITE`: at evidence for either literal, the
`dite` the reflection builds takes the corresponding branch, applied to the proof that `ofTrue`
or `ofFalse` extracts. Same shape as `checkITE.WF`, with four binders instead of two. -/
theorem Reflection.checkNatDITE.WF {c : VContext} {s : VState} {r : Reflection}
    {fail : ∀ {α}, M α} (w : Reflection.WF c r) (hnil : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    {toDec' : VExpr} (htoDec : c.TrExprS r.toDec toDec') (htoDecC : toDec'.ClosedN)
    (htypeOK : CondOK r.type) (htoDecOK : CondOK r.toDec)
    (hditeOK : CondOK r.natDITE) (hofTrueOK : CondOK r.ofTrue) (hofFalseOK : CondOK r.ofFalse)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (r.checkNatDITE fail).WF c s fun _ _ => w.WF_dite toDec' ∧ w.DITE_T toDec' ∧
      (∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ (.const ``Not []) (.const ``Not [])) ∧
      (∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ (.const ``Not [])
        (.forallE (.sort .zero) (.sort .zero))) := by
  have hfailb : ∀ {α β} {k : α → M β} {c s Q}, (fail >>= k).WF c s Q :=
    .bind (hfail (Q := fun _ _ => False)) fun _ _ _ h => h.elim
  have hnil' : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  unfold Reflection.checkNatDITE
  -- `Not : Prop → Prop`
  refine .bind (checkType.WF (by simp [FVarsIn]))
    fun _ _ _ ⟨Not', notTy', _, hNotTr, hNotTyTr, hNotT⟩ => ?_
  refine .bind (isDefEq.WF hNotTyTr TrExprS.propProp) fun _ _ _ hnotarr => ?_
  split <;> [rename_i h1; exact hfailb]
  obtain ⟨rfl, -⟩ := hNotTr.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  have hNotTr' {Δ} : TrExprS c.venv c.lparams Δ q(Not) vexpr(Not) :=
    (hNotTr.const0_inv (Us' := c.lparams) (Δ' := Δ)).2
  have hNotT' {Γ} : c.venv.HasType c.lparams.length Γ vexpr(Not)
      (.forallE (.sort .zero) (.sort .zero)) := by
    refine VEnv.HasType.weak0 c.Ewf ?_
    rw [← hnil']
    exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hnotarr h1) hNotT
  -- the `dite` gadget's type
  refine .bind (checkType.WF (CondOK.fvarsIn hditeOK))
    fun _ _ _ ⟨d₀, dTy', _, hdTr, hdTyTr, hdT⟩ => ?_
  refine .bind (isDefEq.WF hdTyTr
      (TrExprS.reflDiteType w hnil hbool hnat htypeOK hNotTr' hNotT' c.Δwf.toCtx))
    fun _ _ _ hdarr => ?_
  split <;> [rename_i h2; exact hfailb]
  -- `ofTrue : ∀ p, type p true → p` and `ofFalse : ∀ p, type p false → ¬p`
  refine .bind (checkType.WF (CondOK.fvarsIn hofTrueOK))
    fun _ _ _ ⟨oT, oTty, _, hoTTr, hoTtyTr, hoTT⟩ => ?_
  refine .bind (isDefEq.WF hoTtyTr
      (TrExprS.reflOfType w hnil hbool htypeOK true .bvar1 (.bvar (.succ .zero))))
    fun _ _ _ hoTarr => ?_
  split <;> [rename_i h3; exact hfailb]
  refine .bind (checkType.WF (CondOK.fvarsIn hofFalseOK))
    fun _ _ _ ⟨oF, oFty, _, hoFTr, hoFtyTr, hoFT⟩ => ?_
  refine .bind (isDefEq.WF hoFtyTr
      (TrExprS.reflOfType w hnil hbool htypeOK false
        (.app hNotT' (.bvar (.succ .zero)) hNotTr' .bvar1) (.app hNotT' (.bvar (.succ .zero)))))
    fun _ _ _ hoFarr => ?_
  split <;> [rename_i h4; exact hfailb]
  have htypeT : c.venv.HasType c.lparams.length [] w.type'
      vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [hnil'] at h; exact h
  have htw {Γ} : c.venv.HasType c.lparams.length Γ w.type' vexpr(Prop → Bool → Prop) :=
    .weak0 c.Ewf htypeT
  have hnatT {Γ} (h : OnCtx Γ (c.venv.IsType c.lparams.length)) :
      c.venv.IsType c.lparams.length Γ VExpr.nat := c.hasPrimitives.natIsType' c.Ewf hnat h
  -- the `p`, `a` and `b` binders
  refine M.WF.withMLC_self ?_
  simp only
  refine M.WF.withLocalDecl (m := c.mlctx) (ty := Expr.sort Level.zero)
    (ty' := VExpr.sort .zero) (.sort rfl) ⟨_, .sort (l := .zero) trivial⟩ .rfl ?_
  intro idp cwfp s2 hs2 hres2
  have hp0 : (c.withMLC _ (wf := cwfp)).TrExprS (.fvar idp) (.bvar 0) :=
    .fvar VLCtx.find?_vlam_self
  have hp0T : (c.withMLC _ (wf := cwfp)).HasType (.bvar 0) (.sort .zero) := .bvar .zero
  have hΓp := (c.withMLC _ (wf := cwfp)).Δwf.toCtx
  let Ta : TrTy c.venv c.lparams (c.withMLC _ (wf := cwfp)).vlctx
      (.arrow (.fvar idp) (.const ``Nat [])) :=
    TrTy.forallE (.of hp0 ⟨_, hp0T⟩)
      (.of (c.hasPrimitives.trNat c.Ewf hnat) (hnatT ⟨hΓp, _, hp0T⟩))
  refine M.WF.withLocalDecl (ty' := .forallE (.bvar 0) .nat) Ta.trS Ta.isType .rfl ?_
  intro ida cwfa s3 hs3 hres3
  have ha0 : (c.withMLC _ (wf := cwfa)).TrExprS (.fvar ida) (.bvar 0) :=
    .fvar VLCtx.find?_vlam_self
  have hp1 := hp0.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
  have hp1T : (c.withMLC _ (wf := cwfa)).HasType (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have hΓa := (c.withMLC _ (wf := cwfa)).Δwf.toCtx
  have hnotp : (c.withMLC _ (wf := cwfa)).HasType (vexpr(Not).app (.bvar 1))
      (.sort .zero) := .app hNotT' hp1T
  let Tb : TrTy c.venv c.lparams (c.withMLC _ (wf := cwfa)).vlctx
      (.arrow (mkApp (.const ``Not []) (.fvar idp)) (.const ``Nat [])) :=
    TrTy.forallE (.of (.app hNotT' hp1T hNotTr' hp1) ⟨_, hnotp⟩)
      (.of (c.hasPrimitives.trNat c.Ewf hnat) (hnatT ⟨hΓa, _, hnotp⟩))
  refine M.WF.withLocalDecl (ty' := .forallE (vexpr(Not).app (.bvar 1)) .nat)
    Tb.trS Tb.isType .rfl ?_
  intro idb cwfb s4 hs4 hres4
  have hΓb := (c.withMLC _ (wf := cwfb)).Δwf.toCtx
  have hb0 : (c.withMLC _ (wf := cwfb)).TrExprS (.fvar idb) (.bvar 0) :=
    .fvar VLCtx.find?_vlam_self
  have ha1 := ha0.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfb.wf.tr.wf
  have hp2 := hp1.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfb.wf.tr.wf
  have hp2T : (c.withMLC _ (wf := cwfb)).HasType (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  -- the gadget's type and shape, and the two extractors' types
  have hdT' : c.venv.HasType c.lparams.length [] d₀
      (.forallE (.sort .zero) (.forallE .bool
        (.forallE ((w.type'.app (.bvar 1)).app (.bvar 0))
          (.forallE (.forallE (.bvar 2) .nat)
            (.forallE (.forallE (vexpr(Not).app (.bvar 3)) .nat) .nat))))) := by
    rw [← hnil']; exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hdarr h2) hdT
  have hshape := Reflection.natDITE_tr w hnil htypeOK htoDecOK htoDec
    (by rw [← hnil]; exact hdTr)
  have hdC : d₀.ClosedN := (hdT'.closedN' c.Ewf.ordered.closed trivial).1
  have hoT' : c.venv.HasType c.lparams.length [] oT
      (.forallE (.sort .zero)
        (.forallE ((w.type'.app (.bvar 0)).app (.boolLit true)) (.bvar 1))) := by
    rw [← hnil']; exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hoTarr h3) hoTT
  have hoF' : c.venv.HasType c.lparams.length [] oF
      (.forallE (.sort .zero)
        (.forallE ((w.type'.app (.bvar 0)).app (.boolLit false))
          (vexpr(Not).app (.bvar 1)))) := by
    rw [← hnil']; exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hoFarr h4) hoFT
  -- the `H` binder's type, at either literal
  have hlit {Δ} bb : TrExprS c.venv c.lparams Δ (toExpr bb) (.boolLit bb) ∧
      c.venv.HasType c.lparams.length Δ.toCtx (.boolLit bb) .bool :=
    TrExprS.boolLit c.hasPrimitives hbool bb
  have hblitΓ {Γ} bb : c.venv.HasType c.lparams.length Γ (VExpr.boolLit bb) .bool :=
    .weak0 c.Ewf (TrExprS.boolLit (Us := c.lparams) (Δ := []) c.hasPrimitives hbool bb).2
  have htypeTrb {Δ} : TrExprS c.venv c.lparams Δ r.type w.type' :=
    TrExprS.of_nil_any c.Ewf (CondOK.noProj htypeOK) (by rw [← hnil]; exact w.htype)
  have hHtyT bb : (c.withMLC _ (wf := cwfb)).HasType
      ((w.type'.app (.bvar 2)).app (.boolLit bb)) (.sort .zero) :=
    .app (.app htw hp2T) (hlit bb).2
  have hHtyTr bb : (c.withMLC _ (wf := cwfb)).TrExprS
      (mkApp2 r.type (.fvar idp) (toExpr bb))
      ((w.type'.app (.bvar 2)).app (.boolLit bb)) :=
    .app (.app htw hp2T) (hlit bb).2 (.app htw hp2T htypeTrb hp2) (hlit bb).1
  -- the checked equation's left-hand side, as a translation, and its type
  have block (bb : Bool) (idH : FVarId)
      (cwfH : c.MLCWF (.vlam idH `H (mkApp2 r.type (.fvar idp) (toExpr bb))
        ((w.type'.app (.bvar 2)).app (.boolLit bb)) .default
        (.vlam idb `b (.arrow (mkApp (.const ``Not []) (.fvar idp)) (.const ``Nat []))
          (.forallE (vexpr(Not).app (.bvar 1)) .nat) .default
          (.vlam ida `a (.arrow (.fvar idp) (.const ``Nat []))
            (.forallE (.bvar 0) .nat) .default
            (.vlam idp `p (Expr.sort Level.zero) (VExpr.sort .zero) .default c.mlctx))))) :
      (c.withMLC _ (wf := cwfH)).TrExprS
        (mkApp5 r.natDITE (.fvar idp) (toExpr bb) (.fvar idH) (.fvar ida) (.fvar idb))
        (d₀.appN [.bvar 3, .boolLit bb, .bvar 0, .bvar 2, .bvar 1]) := by
    have hΓH := (c.withMLC _ (wf := cwfH)).Δwf.toCtx
    have hp3 := hp2.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    have ha2 := ha1.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    have hb1 := hb0.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    have hH0 : (c.withMLC _ (wf := cwfH)).TrExprS (.fvar idH) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    have hdTrH : (c.withMLC _ (wf := cwfH)).TrExprS r.natDITE d₀ :=
      TrExprS.of_nil_any c.Ewf.ordered
        (CondOK.noProj hditeOK)
        (by rw [← hnil]; exact hdTr)
    have hdTH := VEnv.HasType.weak0 (Γ := (c.withMLC _ (wf := cwfH)).vlctx.toCtx)
      c.Ewf hdT'
    have hargs : VExpr.ArgsTyped c.venv c.lparams.length
        (c.withMLC _ (wf := cwfH)).vlctx.toCtx
        [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0),
          .forallE (.bvar 2) .nat, .forallE (vexpr(Not).app (.bvar 3)) .nat] .id
        [.bvar 3, .boolLit bb, .bvar 0, .bvar 2, .bvar 1] := by
      have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
      refine .cons (by simpa using (.bvar (.succ (.succ (.succ .zero))) :
          c.venv.HasType c.lparams.length _ (VExpr.bvar 3) (VExpr.sort .zero)))
        (.cons (by simpa using (hlit bb).2) (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
      · have h : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
            (.bvar 0) (((w.type'.app (.bvar 2)).app (.boolLit bb)).lift) := .bvar .zero
        have hbc : (VExpr.boolLit bb).ClosedN := by cases bb <;> trivial
        simpa [VExpr.lift, VExpr.liftN, liftVar, VExpr.Subst.cons, VExpr.Subst.id,
          htc.liftN_eq (Nat.zero_le _), hbc.liftN_eq (Nat.zero_le _),
          htc.subst_eq', hbc.subst_eq'] using h
      · have h : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
            (.bvar 2) (VExpr.forallE (.bvar 3) .nat) := .bvar (.succ (.succ .zero))
        simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using h
      · have h : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
            (.bvar 1) (VExpr.forallE (vexpr(Not).app (.bvar 3)) .nat) :=
          .bvar (.succ .zero)
        simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using h
    have hd5 := VEnv.HasType.appN_forallEs hargs (by simpa using hdTH)
    exact TrExprS.appN c.Ewf.orderedStrong hΓH hdTrH
      (.cons hp3 (.cons (hlit bb).1 (.cons hH0 (.cons ha2 (.cons hb1 .nil))))) ⟨_, hd5⟩
  -- the context the two checks are run in, as a telescope over `[]`
  have hAsCtx bb : OnCtx [(w.type'.app (.bvar 2)).app (.boolLit bb),
      .forallE (vexpr(Not).app (.bvar 1)) .nat, .forallE (.bvar 0) .nat, .sort .zero]
      (c.venv.IsType c.lparams.length) := by
    have h1 : OnCtx [VExpr.sort .zero] (c.venv.IsType c.lparams.length) :=
      ⟨trivial, _, .sort trivial⟩
    have h2 : OnCtx [VExpr.forallE (.bvar 0) .nat, .sort .zero] _ :=
      ⟨h1, _, .forallEDF (.bvar .zero) (hnatT (Γ := [VExpr.bvar 0, VExpr.sort .zero])
        ⟨h1, _, .bvar .zero⟩).choose_spec⟩
    have hnp : c.venv.HasType c.lparams.length
        [VExpr.forallE (.bvar 0) .nat, VExpr.sort .zero]
        (vexpr(Not).app (.bvar 1)) (.sort .zero) :=
      VEnv.HasType.app hNotT' (.bvar (.succ .zero))
    have h2' : OnCtx (vexpr(Not).app (.bvar 1) ::
        [VExpr.forallE (.bvar 0) .nat, VExpr.sort .zero]) (c.venv.IsType c.lparams.length) :=
      ⟨h2, _, hnp⟩
    have h3 : OnCtx (VExpr.forallE (vexpr(Not).app (.bvar 1)) .nat ::
        [VExpr.forallE (.bvar 0) .nat, VExpr.sort .zero]) (c.venv.IsType c.lparams.length) :=
      ⟨h2, _, .forallEDF hnp (hnatT h2').choose_spec⟩
    exact ⟨h3, _, .app (.app htw (.bvar (.succ (.succ .zero)))) (hblitΓ bb)⟩
  -- the right-hand side of each check: the branch applied to the extracted proof
  have rhs (bb : Bool) (of' : VExpr) (ofSrc : Expr) (cod : VExpr) (idH : FVarId)
      (cwfH : c.MLCWF (.vlam idH `H (mkApp2 r.type (.fvar idp) (toExpr bb))
        ((w.type'.app (.bvar 2)).app (.boolLit bb)) .default
        (.vlam idb `b (.arrow (mkApp (.const ``Not []) (.fvar idp)) (.const ``Nat []))
          (.forallE (vexpr(Not).app (.bvar 1)) .nat) .default
          (.vlam ida `a (.arrow (.fvar idp) (.const ``Nat []))
            (.forallE (.bvar 0) .nat) .default
            (.vlam idp `p (Expr.sort Level.zero) (VExpr.sort .zero) .default c.mlctx)))))
      (hofTr : TrExprS c.venv c.lparams c.vlctx ofSrc of') (hofOK : noProj ofSrc)
      (hofT : c.venv.HasType c.lparams.length [] of'
        (.forallE (.sort .zero) (.forallE ((w.type'.app (.bvar 0)).app (.boolLit bb)) cod))) :
      (c.withMLC _ (wf := cwfH)).TrExprS (mkApp2 ofSrc (.fvar idp) (.fvar idH))
        ((of'.app (.bvar 3)).app (.bvar 0)) ∧
      c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
        ((of'.app (.bvar 3)).app (.bvar 0))
        (cod.subst ((VExpr.Subst.id.cons (.bvar 3)).cons (.bvar 0))) := by
    have hΓH := (c.withMLC _ (wf := cwfH)).Δwf.toCtx
    have hp3 := hp2.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    have hH0 : (c.withMLC _ (wf := cwfH)).TrExprS (.fvar idH) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
    have hbc : (VExpr.boolLit bb).ClosedN := by cases bb <;> trivial
    have hargs2 : VExpr.ArgsTyped c.venv c.lparams.length
        (c.withMLC _ (wf := cwfH)).vlctx.toCtx
        [.sort .zero, (w.type'.app (.bvar 0)).app (.boolLit bb)] .id [.bvar 3, .bvar 0] := by
      refine .cons (by simpa using (.bvar (.succ (.succ (.succ .zero))) :
          c.venv.HasType c.lparams.length _ (VExpr.bvar 3) (VExpr.sort .zero))) (.cons ?_ .nil)
      have h : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
          (.bvar 0) (((w.type'.app (.bvar 2)).app (.boolLit bb)).lift) := .bvar .zero
      simpa [VExpr.lift, VExpr.liftN, liftVar, VExpr.Subst.cons, VExpr.Subst.id,
        htc.liftN_eq (Nat.zero_le _), hbc.liftN_eq (Nat.zero_le _),
        htc.subst_eq', hbc.subst_eq'] using h
    have hofTH := hofT.weak0 (Γ := (c.withMLC _ (wf := cwfH)).vlctx.toCtx) c.Ewf
    have hap := VEnv.HasType.appN_forallEs hargs2 (by simpa using hofTH)
    refine ⟨?_, hap⟩
    exact TrExprS.appN c.Ewf.orderedStrong hΓH
      (TrExprS.of_nil_any c.Ewf.ordered hofOK (by rw [← hnil]; exact hofTr))
      (.cons hp3 (.cons hH0 .nil)) ⟨_, hap⟩
  -- each check, generalized away from the four binders it was run under
  have hgen (bb : Bool) (of' : VExpr) (idH : FVarId)
      (cwfH : c.MLCWF (.vlam idH `H (mkApp2 r.type (.fvar idp) (toExpr bb))
        ((w.type'.app (.bvar 2)).app (.boolLit bb)) .default
        (.vlam idb `b (.arrow (mkApp (.const ``Not []) (.fvar idp)) (.const ``Nat []))
          (.forallE (vexpr(Not).app (.bvar 1)) .nat) .default
          (.vlam ida `a (.arrow (.fvar idp) (.const ``Nat []))
            (.forallE (.bvar 0) .nat) .default
            (.vlam idp `p (Expr.sort Level.zero) (VExpr.sort .zero) .default c.mlctx)))))
      (hofC : of'.ClosedN)
      (heq : (c.withMLC _ (wf := cwfH)).IsDefEqU
        (d₀.appN [.bvar 3, .boolLit bb, .bvar 0, .bvar 2, .bvar 1])
        ((if bb then VExpr.bvar 2 else .bvar 1).app ((of'.app (.bvar 3)).app (.bvar 0)))) :
      w.DiteEq d₀ of' bb := fun E Γ p H t e hΓ hp ht he hH => by
    have hbc : (VExpr.boolLit bb).ClosedN := by cases bb <;> trivial
    have heq' : c.venv.IsDefEqU c.lparams.length
        ((w.type'.app (.bvar 2)).app (.boolLit bb) ::
          VExpr.forallE (vexpr(Not).app (.bvar 1)) .nat ::
          VExpr.forallE (.bvar 0) .nat :: VExpr.sort .zero :: c.vlctx.toCtx) _ _ := heq
    rw [hnil'] at heq'
    have hargs : VExpr.ArgsTyped E.venv c.lparams.length Γ
        [.sort .zero, .forallE (.bvar 0) .nat,
          .forallE (vexpr(Not).app (.bvar 1)) .nat,
          (w.type'.app (.bvar 2)).app (.boolLit bb)] .id [p, t, e, H] := by
      have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
      refine .cons (by simpa using hp) (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
      · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using ht
      · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using he
      · simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq', hbc.subst_eq'] using hH
    have h := Reflection.WF.genTele (c := c) E
      (As := [.sort .zero, .forallE (.bvar 0) .nat,
        .forallE (vexpr(Not).app (.bvar 1)) .nat,
        (w.type'.app (.bvar 2)).app (.boolLit bb)])
      (by simpa using hAsCtx bb) heq'
      (by simp [VExpr.appN, VExpr.ClosedN, hdC.mono (Nat.zero_le 4), hbc.mono (Nat.zero_le 4)])
      (by cases bb <;> simp [VExpr.ClosedN, hofC.mono (Nat.zero_le 4)])
      hΓ hargs
    simp only [VExpr.appN, VExpr.subst_app] at h
    rw [hdC.subst_eq', hbc.subst_eq', hofC.subst_eq'] at h
    cases bb <;>
      simpa [VExpr.appN, VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id] using h
  have hoTC : oT.ClosedN := (hoT'.closedN' c.Ewf.ordered.closed trivial).1
  have hoFC : oF.ClosedN := (hoF'.closedN' c.Ewf.ordered.closed trivial).1
  -- the two equation blocks
  refine .bind (Q := fun _ _ => w.DiteEq d₀ oT true) ?_ fun _ _ _ hTrue => ?_
  · refine M.WF.withLocalDecl (hHtyTr true) ⟨_, hHtyT true⟩ .rfl ?_
    intro idH cwfH s5 hs5 hres5
    obtain ⟨hrhsTr, hrhsT⟩ := rhs true oT r.ofTrue (.bvar 1) idH cwfH hoTTr
      (CondOK.noProj hofTrueOK) hoT'
    have hrhsT' : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
        ((oT.app (.bvar 3)).app (.bvar 0)) (.bvar 3) := by
      simpa [VExpr.Subst.cons, VExpr.Subst.id, VLCtx.toCtx] using hrhsT
    have ha2 := ha1.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
    refine .bind (isDefEq.WF (block true idH cwfH)
        (.app (.bvar (.succ (.succ .zero))) hrhsT' ha2 hrhsTr)) fun _ _ _ heq => ?_
    split <;> [rename_i h5; exact hfail]
    exact .pure (hgen true oT idH cwfH hoTC (heq h5))
  refine M.WF.withLocalDecl (hHtyTr false) ⟨_, hHtyT false⟩ .rfl ?_
  intro idH cwfH s5 hs5 hres5
  obtain ⟨hrhsTr, hrhsT⟩ := rhs false oF r.ofFalse (vexpr(Not).app (.bvar 1))
    idH cwfH hoFTr
    (CondOK.noProj hofFalseOK) hoF'
  have hrhsT' : c.venv.HasType c.lparams.length (c.withMLC _ (wf := cwfH)).vlctx.toCtx
      ((oF.app (.bvar 3)).app (.bvar 0)) (vexpr(Not).app (.bvar 3)) := by
    simpa [VExpr.Subst.cons, VExpr.Subst.id, VLCtx.toCtx] using hrhsT
  have hb1 := hb0.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfH.wf.tr.wf
  refine .bind (isDefEq.WF (block false idH cwfH)
      (.app (.bvar (.succ .zero)) hrhsT' hb1 hrhsTr)) fun _ _ _ heq => ?_
  split <;> [rename_i h5; exact hfail]
  have hFalse : w.DiteEq d₀ oF false := hgen false oF idH cwfH hoFC (heq h5)
  refine .pure ⟨⟨oT, oF, hoTTr, hoFTr, ?_⟩, fun E Γ p H bb hΓ hp hbb hH => ?_, hNotTr', hNotT'⟩
  case refine_2 =>
    -- the gadget is well typed at *any* boolean, which a consumer needs to build it
    have hdTΓ := (E.monoT hdT').weak0 (Γ := Γ) E.wf.ordered
    rw [hshape] at hdTΓ
    obtain ⟨hΓ1, hb1⟩ := VExpr.WF.lam_inv' E.wf hΓ ⟨_, hdTΓ⟩
    obtain ⟨hΓ2, hb2⟩ := VExpr.WF.lam_inv' E.wf hΓ1 hb1
    obtain ⟨hΓ3, hb3⟩ := VExpr.WF.lam_inv' E.wf hΓ2 hb2
    have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
    have hargs3 : VExpr.ArgsTyped E.venv c.lparams.length Γ
        [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0)] .id [p, bb, H] := by
      refine .cons (by simpa using hp) (.cons (by simpa using hbb) (.cons ?_ .nil))
      simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq'] using hH
    have h3 := VEnv.HasType.appN_forallEs hargs3
      (by simpa using VEnv.HasType.weak0 (Γ := Γ) E.wf (E.monoT hdT'))
    have hbeta := (VExpr.lams_appN' E.wf hΓ (by simpa using hΓ3) (.id E.wf hΓ) hargs3 hb3).2
    simp only [VExpr.subst_id, VExpr.lams_nil] at hbeta
    rw [← hshape] at hbeta
    have h5 := VEnv.HasType.defeqU_l E.wf hΓ hbeta h3
    simp only [VExpr.subst_app, VExpr.subst_const] at h5
    rw [htoDecC.subst_eq'] at h5
    simpa [VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id, VExpr.subst,
      VExpr.Subst.lift, VExpr.lift, VExpr.nat, VExpr.liftN, liftVar] using h5
  intro E Γ p H t e bb hΓ hp hH ht he
  -- the gadget applied to all five arguments, and its beta-reduct
  have htc : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
  have hbc : (VExpr.boolLit bb).ClosedN := by cases bb <;> trivial
  have hargs5 : VExpr.ArgsTyped E.venv c.lparams.length Γ
      [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0),
        .forallE (.bvar 2) .nat, .forallE (vexpr(Not).app (.bvar 3)) .nat] .id
      [p, .boolLit bb, H, t, e] := by
    refine .cons (by simpa using hp) (.cons (by simpa using E.monoT (hblitΓ bb)) (.cons ?_ (.cons ?_
      (.cons ?_ .nil))))
    · simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq', hbc.subst_eq'] using hH
    · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using ht
    · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, VExpr.Subst.lift] using he
  have hd5 := VEnv.HasType.appN_forallEs hargs5
    (by simpa using VEnv.HasType.weak0 (Γ := Γ) E.wf (E.monoT hdT'))
  -- the beta at the gadget's three binders, then the two branches
  have hargs3 : VExpr.ArgsTyped E.venv c.lparams.length Γ
      [.sort .zero, .bool, (w.type'.app (.bvar 1)).app (.bvar 0)] .id [p, .boolLit bb, H] := by
    refine .cons (by simpa using hp) (.cons (by simpa using E.monoT (hblitΓ bb)) (.cons ?_ .nil))
    simpa [VExpr.Subst.cons, VExpr.Subst.id, htc.subst_eq', hbc.subst_eq'] using hH
  have hdTΓ := VEnv.HasType.weak0 (Γ := Γ) E.wf (E.monoT hdT')
  rw [hshape] at hdTΓ
  obtain ⟨hΓ1, hb1'⟩ := VExpr.WF.lam_inv' E.wf hΓ ⟨_, hdTΓ⟩
  obtain ⟨hΓ2, hb2'⟩ := VExpr.WF.lam_inv' E.wf hΓ1 hb1'
  obtain ⟨hΓ3, hb3'⟩ := VExpr.WF.lam_inv' E.wf hΓ2 hb2'
  have hbeta := (VExpr.lams_appN' E.wf hΓ (by simpa using hΓ3) (.id E.wf hΓ) hargs3 hb3').2
  simp only [VExpr.subst_id] at hbeta
  have hwf5 : VExpr.WF E.venv c.lparams.length Γ
      (d₀.appN [p, .boolLit bb, H, t, e]) := ⟨_, hd5⟩
  have hstep := VEnv.IsDefEqU.appN E.wf hΓ (vs := [t, e]) (hshape ▸ hbeta)
    (by simpa [VExpr.appN] using hwf5)
  have hde : w.DiteEq d₀ (if bb then oT else oF) bb := by cases bb; exacts [hFalse, hTrue]
  have hdeb : E.venv.IsDefEqU c.lparams.length Γ (d₀.appN [p, .boolLit bb, H, t, e])
      (if bb then t.app ((oT.app p).app H) else e.app ((oF.app p).app H)) := by
    have h := hde E hΓ hp ht he hH
    cases bb <;> simpa using h
  refine VEnv.IsDefEqU.trans E.wf hΓ ?_
    (VEnv.IsDefEqU.trans E.wf hΓ hstep.symm hdeb)
  -- the two sides of the beta agree on the nose once the closed pieces are left alone
  obtain ⟨A, hA⟩ := hstep
  refine ⟨A, ?_⟩
  have h2 := hA.hasType.2
  simp [VExpr.appN, diteApp, VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id,
    htoDecC.subst_eq'] at h2 ⊢
  exact h2

/-- `Condition.WF.WF_dite` for a `reflectNatNat`, from the reflection's own `WF_dite`. Same
bridge as `reflect_ite`, with the branches under binders: the consumer's are lambdas, the
reflection's are the functions they denote, and the proof each branch is applied to is the one
`ofTrue`/`ofFalse` extracts. -/
theorem Condition.WF.reflect_dite {prop dec asBool proof : Expr}
    {prop' dec' asBool' proof' toDec' : VExpr} (w : Reflection.WF c reflect)
    (w' : Condition.WF c ⟨prop, dec, .reflectNatNat asBool reflect proof⟩)
    (hw'dec : w'.dec' = dec') (hnil : c.vlctx = []) (hnat : c.venv.contains ``Nat)
    (hWD : w.WF_dite toDec') (hDT : w.DITE_T toDec')
    (hNotTr : ∀ {Δ}, TrExprS c.venv c.lparams Δ q(Not) vexpr(Not))
    (hNotT : ∀ {Γ}, c.venv.HasType c.lparams.length Γ vexpr(Not) vexpr(Prop → Prop))
    (hpropTrΓ : ∀ {Δ}, TrExprS c.venv c.lparams Δ prop prop')
    (hdecTrΓ : ∀ {Δ}, TrExprS c.venv c.lparams Δ dec dec')
    (htypeTΓ : ∀ (E : c.Ext) {Γ},
      E.venv.HasType c.lparams.length Γ w.type' vexpr(Prop → Bool → Prop))
    (H : ∀ (E : c.Ext) ⦃Γ⦄, OnCtx Γ (E.venv.IsType c.lparams.length) → ∀ {x y},
      E.venv.HasType c.lparams.length Γ x .nat → E.venv.HasType c.lparams.length Γ y .nat →
      E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) vexpr(Prop) ∧
      E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
      E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
        ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
      E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
          ((proof'.app x).app y))) :
    w'.WF_dite := by
  obtain ⟨oT, oF, hoTTr, hoFTr, hWDeq⟩ := hWD
  intro m cwfm t e args P t' e' args' hargs hargsT hP hPT ht htT he heT
  have hΓm := (c.withMLC m).Δwf.toCtx
  obtain ⟨x, y, rfl, hxT, hyT⟩ : ∃ x y, args' = [x, y] ∧
      c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx x .nat ∧
      c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx y .nat := by
    cases hargsT with | cons h1 h2; cases h2 with | cons h3 h4; cases h4; exact ⟨_, _, rfl, h1, h3⟩
  -- the condition, the decision and the evidence at those arguments
  have ⟨hpT, hblT, hHT, hdecEq⟩ := H c.self hΓm hxT hyT
  have htypeC : w.type'.ClosedN := by
    have h : c.venv.HasType .. := w.typeT
    rw [hnil] at h
    exact (h.closedN' c.Ewf.ordered.closed trivial).1
  -- the consumer's condition agrees with the one built from the pieces
  have hpropApp : (c.withMLC m).TrExprS (mkAppN prop args) ((prop'.app x).app y) := by
    generalize hal : args.toList = al at hargs
    obtain ⟨xs, ys, rfl, hxTr, hyTr⟩ : ∃ xs ys, al = [xs, ys] ∧
        (c.withMLC m).TrExprS xs x ∧ (c.withMLC m).TrExprS ys y := by
      cases hargs with | cons h1 h2; cases h2 with | cons h3 h4; cases h4; exact ⟨_, _, rfl, h1, h3⟩
    rw [Expr.mkAppN_eq, hal]
    exact TrExprS.appN c.Ewf.orderedStrong hΓm hpropTrΓ (.cons hxTr (.cons hyTr .nil)) ⟨_, hpT⟩
  have hPeq : (c.withMLC m).IsDefEqU P ((prop'.app x).app y) :=
    hP.uniq c.Ewf (.refl c.Ewf (c.withMLC m).Δwf) hpropApp
  -- the evidence and the decision, at the consumer's own condition
  have hToDecT : w.ToDecT toDec' := hDT.toDecT
  have hHT' : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      ((proof'.app x).app y) ((w.type'.app P).app ((asBool'.app x).app y)) := by
    refine VEnv.HasType.defeqU_r c.Ewf hΓm ?_ hHT
    exact VEnv.IsDefEqU.appN c.Ewf hΓm (vs := [(asBool'.app x).app y])
      (VEnv.IsDefEqU.app_arg c.Ewf hΓm (htypeTΓ c.self) hpT hPeq.symm)
      ⟨_, VEnv.HasType.app (VEnv.HasType.app (htypeTΓ c.self) hpT) hblT⟩
  obtain ⟨_, _, _, _, _, _, ⟨htd1, hp1⟩, ⟨htd2, hb2⟩, -⟩ := hToDecT.spine c.self hΓm hpT hblT hHT
  have hdecEq' : c.venv.IsDefEqU c.lparams.length (c.withMLC m).vlctx.toCtx
      ((dec'.app x).app y)
      (((toDec'.app P).app ((asBool'.app x).app y)).app ((proof'.app x).app y)) := by
    refine VEnv.IsDefEqU.trans c.Ewf hΓm hdecEq ?_
    refine VEnv.IsDefEqU.appN c.Ewf hΓm (vs := [(proof'.app x).app y]) ?_
      (hToDecT c.self hΓm hpT hblT hHT)
    exact VEnv.IsDefEqU.appN c.Ewf hΓm (vs := [(asBool'.app x).app y])
      (VEnv.IsDefEqU.app_arg c.Ewf hΓm htd1 hp1 hPeq.symm) ⟨_, VEnv.HasType.app htd2 hb2⟩
  -- the two branches as functions, and the gadget at the consumer's decision
  have htlam : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      (.lam P t') (.forallE P .nat) := .lam hPT htT
  have hNotP : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      (vexpr(Not).app P) (.sort .zero) := .app hNotT hPT
  have helam : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      (.lam (vexpr(Not).app P) e')
      (.forallE (vexpr(Not).app P) .nat) := .lam hNotP heT
  have hd3 := hDT c.self hΓm hPT hblT hHT'
  obtain ⟨A₀, B₀, hf₀, ha₀⟩ := hd3.app_inv c.Ewf.orderedStrong hΓm
  have hd3' : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      ((((VExpr.const ``dite [.succ .zero]).app .nat).app P).app ((dec'.app x).app y))
      (.forallE (.forallE P .nat)
        (.forallE (.forallE (vexpr(Not).app P.lift) .nat) .nat)) :=
    VEnv.HasType.defeqU_l c.Ewf hΓm
      (VEnv.IsDefEqU.app_arg c.Ewf hΓm hf₀ ha₀ hdecEq'.symm) hd3
  have hd4 := VEnv.HasType.app hd3' htlam
  have hd5 := VEnv.HasType.app hd4 (by
    simpa [VExpr.inst, VExpr.inst_lift] using helam)
  -- the translation of the conditional the consumer builds
  have hdecApp : (c.withMLC m).TrExprS (mkAppN dec args) ((dec'.app x).app y) := by
    generalize hal : args.toList = al at hargs
    obtain ⟨xs, ys, rfl, hxTr, hyTr⟩ : ∃ xs ys, al = [xs, ys] ∧
        (c.withMLC m).TrExprS xs x ∧ (c.withMLC m).TrExprS ys y := by
      cases hargs with
      | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4; exact ⟨_, _, rfl, h1, h3⟩
    rw [Expr.mkAppN_eq, hal]
    have hdecT' : VExpr.WF c.venv c.lparams.length (c.withMLC m).vlctx.toCtx
        ((dec'.app x).app y) := by
      obtain ⟨_, h⟩ := hToDecT c.self hΓm hpT hblT hHT
      exact ⟨_, VEnv.HasType.defeqU_l c.Ewf hΓm hdecEq.symm h⟩
    exact TrExprS.appN c.Ewf.orderedStrong hΓm hdecTrΓ (.cons hxTr (.cons hyTr .nil)) hdecT'
  obtain ⟨_, _, hf₁, -⟩ := hf₀.app_inv c.Ewf.orderedStrong hΓm
  obtain ⟨_, _, hf₂, -⟩ := hf₁.app_inv c.Ewf.orderedStrong hΓm
  obtain ⟨ci, hci, -, hlen⟩ := hf₂.const_inv c.Ewf.orderedStrong hΓm
  have hdCTr : (c.withMLC m).TrExprS (.const ``dite [.succ .zero])
      (.const ``dite [.succ .zero]) := .const hci rfl hlen
  rw [show w'.dec' = dec' from hw'dec]
  refine TrExprS.appN c.Ewf.orderedStrong hΓm hdCTr (
    .cons (c.hasPrimitives.trNat c.Ewf hnat) <|
    .cons hP <| .cons hdecApp <| .cons (.lam ⟨_, hPT⟩ hP ht) <|
    .cons (.lam ⟨_, hNotP⟩ (.app hNotT hPT hNotTr hP) he) .nil) ⟨_, hd5⟩

/-- The gadget `Condition.check` builds, once everything in it is translated. -/
def Condition.check.gadgetV (type' toDec' prop' asBool' proof' : VExpr) : VExpr :=
  VExpr.lams [.nat, .nat]
    ((VExpr.lams [.sort .zero, .bool, (type'.app (.bvar 1)).app (.bvar 0)]
        (((toDec'.app (.bvar 2)).app (.bvar 1)).app (.bvar 0))).appN
      [(prop'.app (.bvar 1)).app (.bvar 0), (asBool'.app (.bvar 1)).app (.bvar 0),
        (proof'.app (.bvar 1)).app (.bvar 0)])

/-- The typing half of `gadget_pieces`, with the gadget's shape spelled out. Two things come out
of `checkType e`, and both are read off the redex: the three arguments are checked against
binders that name `Prop`, `Bool` and `type p b`, which types them; and the redex beta-reduces,
which is what makes the gadget the decision procedure the `e ≡ dec` check compares against.

The typings are proved under the gadget's own two `Nat` binders and moved to the consumer's
arguments by `genTeleT`; the inner beta step likewise travels by `genTele`, while the outer one
is done at the consumer's context directly, since that is where its argument typings live. -/
theorem Condition.check.gadget_types {c : VContext}
    {type' toDec' prop' asBool' proof' eTy' : VExpr} (hnat : c.venv.contains ``Nat)
    (htypeC : type'.ClosedN) (htoDecC : toDec'.ClosedN)
    (hpropC : prop'.ClosedN) (habC : asBool'.ClosedN) (hpfC : proof'.ClosedN)
    (hT : c.venv.HasType c.lparams.length []
      (Condition.check.gadgetV type' toDec' prop' asBool' proof') eTy') :
    ∀ (E : c.Ext) ⦃Γ : List VExpr⦄, OnCtx Γ (E.venv.IsType c.lparams.length) →
      ∀ {x y : VExpr}, E.venv.HasType c.lparams.length Γ x .nat →
      E.venv.HasType c.lparams.length Γ y .nat →
      E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) (.sort .zero) ∧
      E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
      E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
        ((type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
      E.venv.IsDefEqU c.lparams.length Γ
        (((Condition.check.gadgetV type' toDec' prop' asBool' proof').app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
          ((proof'.app x).app y)) := by
  -- closedness of everything in sight, at whatever depth it is met
  have htc k : type'.ClosedN k := htypeC.mono (Nat.zero_le _)
  have htdc k : toDec'.ClosedN k := htoDecC.mono (Nat.zero_le _)
  have hpc k : prop'.ClosedN k := hpropC.mono (Nat.zero_le _)
  have hac k : asBool'.ClosedN k := habC.mono (Nat.zero_le _)
  have hfc k : proof'.ClosedN k := hpfC.mono (Nat.zero_le _)
  -- the gadget's typing, under its two `Nat` binders
  have hΓ0 : OnCtx ([] : List VExpr) (c.venv.IsType c.lparams.length) := trivial
  rw [Condition.check.gadgetV, VExpr.lams, VExpr.lams] at hT
  obtain ⟨hΓ1, hb1⟩ := VExpr.WF.lam_inv' c.Ewf hΓ0 ⟨_, hT⟩
  obtain ⟨hΓ2, hb2⟩ := VExpr.WF.lam_inv' c.Ewf hΓ1 hb1
  simp only [VExpr.lams_nil, VExpr.appN] at hb2
  -- the redex's own type: its binders are what the arguments are checked against
  obtain ⟨_, _, hf₃, ha₃⟩ := VExpr.WF.app_inv c.Ewf hΓ2 hb2
  obtain ⟨_, _, hf₂, ha₂⟩ := VExpr.WF.app_inv c.Ewf hΓ2 ⟨_, hf₃⟩
  obtain ⟨_, _, hf₁, ha₁⟩ := VExpr.WF.app_inv c.Ewf hΓ2 ⟨_, hf₂⟩
  simp only [VExpr.lams] at hf₁
  obtain ⟨⟨_, hAp⟩, _, hLb1⟩ := VExpr.WF.lam_inv c.Ewf hΓ2 ⟨_, hf₁⟩
  have hΓp : OnCtx (_ :: _) (c.venv.IsType c.lparams.length) := ⟨hΓ2, _, hAp⟩
  obtain ⟨⟨_, hAb⟩, _, hLb2⟩ := VExpr.WF.lam_inv c.Ewf hΓp ⟨_, hLb1⟩
  have hΓb : OnCtx (_ :: _) (c.venv.IsType c.lparams.length) := ⟨hΓp, _, hAb⟩
  obtain ⟨⟨_, hAH⟩, _, hLb3⟩ := VExpr.WF.lam_inv c.Ewf hΓb ⟨_, hLb2⟩
  have hΓH : OnCtx (_ :: _) (c.venv.IsType c.lparams.length) := ⟨hΓb, _, hAH⟩
  have hL3T := VEnv.HasType.lam hAH hLb3
  have hL2T := VEnv.HasType.lam hAb hL3T
  have hL1T := VEnv.HasType.lam hAp hL2T
  -- each argument, against the binder it was checked at
  obtain ⟨⟨_, hdom1⟩, -⟩ := (hf₁.uniqU c.Ewf hΓ2 hL1T).forallE_inv c.Ewf hΓ2
  have hpT := VEnv.HasType.defeqU_r c.Ewf hΓ2 ⟨_, hdom1⟩ ha₁
  have hstep1 := VEnv.HasType.app hL1T hpT
  simp [VExpr.inst, VExpr.instVar, htypeC.instN_eq (Nat.zero_le _)] at hstep1
  obtain ⟨⟨_, hdom2⟩, -⟩ := (hf₂.uniqU c.Ewf hΓ2 hstep1).forallE_inv c.Ewf hΓ2
  have hbT := VEnv.HasType.defeqU_r c.Ewf hΓ2 ⟨_, hdom2⟩ ha₂
  have hstep2 := VEnv.HasType.app hstep1 hbT
  simp [VExpr.inst, VExpr.instVar, VExpr.inst_lift, htypeC.instN_eq (Nat.zero_le _)] at hstep2
  obtain ⟨⟨_, hdom3⟩, -⟩ := (hf₃.uniqU c.Ewf hΓ2 hstep2).forallE_inv c.Ewf hΓ2
  have hpfT := VEnv.HasType.defeqU_r c.Ewf hΓ2 ⟨_, hdom3⟩ ha₃
  -- the inner beta step, where the redex lives
  have hargs3 : VExpr.ArgsTyped c.venv c.lparams.length (VExpr.nat :: VExpr.nat :: [])
      [.sort .zero, .bool, (type'.app (.bvar 1)).app (.bvar 0)] .id
      [(prop'.app (.bvar 1)).app (.bvar 0), (asBool'.app (.bvar 1)).app (.bvar 0),
        (proof'.app (.bvar 1)).app (.bvar 0)] := by
    refine .cons (by simpa using hpT) (.cons (by simpa using hbT) (.cons ?_ .nil))
    simpa [VExpr.Subst.cons, VExpr.Subst.id, htypeC.subst_eq'] using hpfT
  have hbetaIn := (VExpr.lams_appN' c.Ewf hΓ2 (by simpa using hΓH) (.id c.Ewf hΓ2) hargs3 ⟨_, hLb3⟩).2
  simp only [VExpr.subst_id] at hbetaIn
  simp only [VExpr.subst, VExpr.Subst.consN, VExpr.Subst.cons, VExpr.Subst.id,
    htoDecC.subst_eq'] at hbetaIn
  -- and now at the consumer's own context and arguments
  intro E Γ hΓ x y hxT hyT
  have hnatIT {Γ'} (h : OnCtx Γ' (c.venv.IsType c.lparams.length)) :
      c.venv.IsType c.lparams.length Γ' VExpr.nat := c.hasPrimitives.natIsType' c.Ewf hnat h
  have hAs : OnCtx [VExpr.nat, VExpr.nat] (c.venv.IsType c.lparams.length) :=
    ⟨⟨trivial, hnatIT trivial⟩, hnatIT ⟨trivial, hnatIT trivial⟩⟩
  have hargs2 : VExpr.ArgsTyped E.venv c.lparams.length Γ [.nat, .nat] .id [x, y] :=
    .cons (by simpa using hxT) (.cons (by simpa using hyT) .nil)
  have hcl2 {f : VExpr} (h : ∀ k, f.ClosedN k) :
      (((f.app (.bvar 1)).app (.bvar 0) : VExpr)).ClosedN 2 :=
    ⟨⟨h 2, Nat.lt_succ_self _⟩, Nat.succ_pos _⟩
  have gen {X A : VExpr} (hX : c.venv.HasType c.lparams.length [.nat, .nat] X A)
      (hXc : X.ClosedN 2) (hAc : A.ClosedN 2) :
      E.venv.HasType c.lparams.length Γ (X.subst ((VExpr.Subst.id.cons x).cons y))
        (A.subst ((VExpr.Subst.id.cons x).cons y)) :=
    Reflection.WF.genTeleT E (As := [.nat, .nat]) (by simpa using hAs) hX hXc hAc hΓ hargs2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, hpropC.subst_eq'] using
      gen hpT (hcl2 hpc) trivial
  · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, habC.subst_eq'] using
      gen hbT (hcl2 hac) trivial
  · simpa [VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id, hpfC.subst_eq', hpropC.subst_eq',
      habC.subst_eq', htypeC.subst_eq'] using
      gen hpfT (hcl2 hfc) ⟨⟨htc 2, hcl2 hpc⟩, hcl2 hac⟩
  -- the outer beta step, then the inner one moved here by `genTele`
  have heTΓ : E.venv.HasType c.lparams.length Γ _ eTy' := (E.monoT hT).weak0 (Γ := Γ) E.wf.ordered
  obtain ⟨hΓg1, hbg1⟩ := VExpr.WF.lam_inv' E.wf hΓ ⟨_, heTΓ⟩
  obtain ⟨hΓg2, hbg2⟩ := VExpr.WF.lam_inv' E.wf hΓg1 hbg1
  have hbetaOut := (VExpr.lams_appN' (As := [VExpr.nat, VExpr.nat]) E.wf hΓ
    (by simpa using hΓg2) (.id E.wf hΓ) hargs2 hbg2).2
  simp only [VExpr.subst_id] at hbetaOut
  have hbetaIn' := Reflection.WF.genTele (c := c) E (As := [.nat, .nat]) (by simpa using hAs)
    hbetaIn
    (by simp [VExpr.appN, VExpr.lams, VExpr.ClosedN, VExpr.bool, htc, htdc, hpc, hac, hfc])
    (by simp [VExpr.ClosedN, htdc, hpc, hac, hfc]) hΓ hargs2
  rw [Condition.check.gadgetV]
  simp only [VExpr.subst, VExpr.appN, VExpr.lams, VExpr.Subst.consN,
    VExpr.Subst.cons, VExpr.Subst.id, htypeC.subst_eq', htoDecC.subst_eq', hpropC.subst_eq',
    habC.subst_eq', hpfC.subst_eq'] at hbetaOut hbetaIn' ⊢
  exact VEnv.IsDefEqU.trans E.wf hΓ hbetaOut hbetaIn'

/-- The whole content of `checkType e`, for the gadget

    e = fun x y : Nat => (fun (p : Prop) (b : Bool) (H : type p b) => toDec p b H)
          (prop x y) (asBool x y) (proof x y)

*Its translation* determines the three pieces': they are read under the gadget's two `Nat`
binders, and `TrExprS.ofClosed` brings those readings down to `[]`, where the rest of the
development lives. So `Condition.check` needs no check of its own for `prop`, `asBool` or
`proof` -- reading them is what the gadget already does.

*Its typing* determines their types. That is what the beta-redex is for: the arguments are
checked against binders that name `Prop`, `Bool` and `type p b`, so a gadget that type checks at
all has pieces of those types, and has them consistent with each other -- which a separate check
of `proof` could assert but not tie to `prop` and `asBool`. Written as the application
`toDec (prop x y) (asBool x y) (proof x y)` it would instead be `toDec`'s *own* type that pinned
them, and nothing checks that: `toDec` is only ever used, inside `ite`/`natDITE`.

Everything is exported at an arbitrary context and arbitrary arguments, since that is where a
consumer needs it: `genTeleT` moves the typings, and the two beta steps -- one per redex -- are
what turns the gadget applied to two naturals into `toDec` at the three pieces. -/
theorem Condition.check.gadget_pieces {c : VContext} {prop asBool proof : Expr} {r : Reflection}
    {e' eTy' : VExpr} (w : Reflection.WF c r) (hnil : c.vlctx = []) (hnat : c.venv.contains ``Nat)
    (hpropOK : CondOK prop) (hasBoolOK : CondOK asBool) (hproofOK : CondOK proof)
    (htypeOK : CondOK r.type) (htoDecOK : CondOK r.toDec)
    (H : TrExprS c.venv c.lparams [] (.lam0 (.const ``Nat []) (.lam0 (.const ``Nat [])
      (mkApp3
        (.lam0 (.sort .zero) (.lam0 (.const ``Bool [])
          (.lam0 (mkApp2 r.type (.bvar 1) (.bvar 0))
            (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0)))))
        (mkApp2 prop (.bvar 1) (.bvar 0)) (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))))) e')
    (hT : c.venv.HasType c.lparams.length [] e' eTy') :
    ∃ prop' asBool' proof' toDec',
      TrExprS c.venv c.lparams [] prop prop' ∧ TrExprS c.venv c.lparams [] asBool asBool' ∧
      TrExprS c.venv c.lparams [] proof proof' ∧ TrExprS c.venv c.lparams [] r.toDec toDec' ∧
      prop'.ClosedN ∧ asBool'.ClosedN ∧ proof'.ClosedN ∧ toDec'.ClosedN ∧
      ∀ (E : c.Ext) ⦃Γ : List VExpr⦄, OnCtx Γ (E.venv.IsType c.lparams.length) →
        ∀ {x y : VExpr}, E.venv.HasType c.lparams.length Γ x .nat →
        E.venv.HasType c.lparams.length Γ y .nat →
        E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) (.sort .zero) ∧
        E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
        E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
          ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
        E.venv.IsDefEqU c.lparams.length Γ ((e'.app x).app y)
          (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
            ((proof'.app x).app y)) := by
  have uniq : ∀ {x : Expr} {v : VExpr}, CondOK x → c.TrExprS x v →
      ∀ {Δ : VLCtx} {u}, TrExprS c.venv c.lparams Δ x u → u = v := by
    intro x v hx hv Δ u hu
    exact TrExprS.of_nil_unique c.Ewf (CondOK.noProj hx) (by rw [← hnil]; exact hv) hu
  -- a closed piece is read the same way at `[]` as it is under the gadget's binders. This is
  -- what makes a check of `toDec` unnecessary: `checkType e` reads it, five binders deep, and
  -- `ofClosed` is what brings that reading back to where everything else lives.
  have desc {Δ₀ x u} (hx : CondOK x) (hu : TrExprS c.venv c.lparams Δ₀ x u)
      (hΔ : OnCtx Δ₀.toCtx (c.venv.IsType c.lparams.length))
      (hwf : VExpr.WF c.venv c.lparams.length Δ₀.toCtx u) :
      u.ClosedN ∧ TrExprS c.venv c.lparams [] x u :=
    TrExprS.ofClosed (Δ := Δ₀) c.Ewf (pre := []) hu rfl (CondOK.noProj hx)
      (CondOK.closed hx) (CondOK.fvarsIn hx) trivial
      (by intro v x A hv; simp [VLCtx.find?] at hv) (by simpa using hΔ) (by simpa using hwf)
  have htypeT : c.venv.HasType c.lparams.length [] w.type'
      vexpr(Prop → Bool → Prop) := by
    have h : c.venv.HasType c.lparams.length c.vlctx.toCtx w.type' _ := w.typeT
    rw [show c.vlctx.toCtx = [] from by rw [hnil]; rfl] at h; exact h
  have htypeC : w.type'.ClosedN := (htypeT.closedN' c.Ewf.ordered.closed trivial).1
  -- the gadget's translation, piece by piece, keeping each binder's and each application's own
  -- side conditions: they are what `desc` runs on
  simp only [Expr.lam0, mkApp3, mkApp2, mkApp] at H
  cases H with | lam hI1 hd1 H
  obtain ⟨rfl, -⟩ := hd1.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  cases H with | lam hI2 hd2 H
  obtain ⟨rfl, -⟩ := hd2.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  have hΓ2 : OnCtx (VExpr.nat :: VExpr.nat :: []) (c.venv.IsType c.lparams.length) :=
    ⟨⟨trivial, hI1⟩, hI2⟩
  cases H with | app _ _ hf hpf
  cases hf with | app _ _ hf2 hab
  cases hf2 with | app _ _ hL hpr
  -- the redex's three binders name the three argument types
  cases hL with | lam hI3 hdp hL1
  cases hdp with | sort hs
  cases by simpa [VLevel.ofLevel] using hs
  cases hL1 with | lam hI4 hdb hL2
  obtain ⟨rfl, -⟩ := hdb.const0_inv (Us' := c.lparams)
    (Δ' := (none, .vlam (.sort .zero)) :: (none, .vlam .nat) :: (none, .vlam .nat) :: c.vlctx)
  cases hL2 with | lam hI5 hdH hL3
  cases hdH with | app _ _ hdH1 hdHb
  cases hdH1 with | app _ _ hdHc hdHp
  cases hdHb with | bvar hb0
  cases hdHp with | bvar hb1
  simp only [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, Option.some.injEq, Prod.mk.injEq] at hb0 hb1
  obtain ⟨rfl, -⟩ := hb0; obtain ⟨rfl, -⟩ := hb1
  cases uniq htypeOK w.htype hdHc
  -- the redex's body is `toDec` at those three binders
  cases hL3 with | app _ _ hL3f hL3a0
  cases hL3f with | app _ _ hL3f2 hL3a1
  cases hL3f2 with | app htdT _ htd hL3a2
  cases hL3a0 with | bvar hc0
  cases hL3a1 with | bvar hc1
  cases hL3a2 with | bvar hc2
  simp only [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, liftVar, Option.some.injEq, Prod.mk.injEq] at hc0 hc1 hc2
  obtain ⟨rfl, -⟩ := hc0; obtain ⟨rfl, -⟩ := hc1; obtain ⟨rfl, -⟩ := hc2
  -- the three arguments
  cases hpf with | app _ _ hpf1 hpf0
  cases hpf1 with | app hpfT _ hpfc hpfx
  cases hab with | app _ _ hab1 hab0
  cases hab1 with | app habT _ habc habx
  cases hpr with | app _ _ hpr1 hpr0
  cases hpr1 with | app hprT _ hprc hprx
  cases hpfx with | bvar h1
  cases hpf0 with | bvar h2
  cases habx with | bvar h3
  cases hab0 with | bvar h4
  cases hprx with | bvar h5
  cases hpr0 with | bvar h6
  simp only [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, Option.some.injEq, Prod.mk.injEq] at h1 h2 h3 h4 h5 h6
  obtain ⟨rfl, -⟩ := h1; obtain ⟨rfl, -⟩ := h2; obtain ⟨rfl, -⟩ := h3
  obtain ⟨rfl, -⟩ := h4; obtain ⟨rfl, -⟩ := h5; obtain ⟨rfl, -⟩ := h6
  -- every piece, brought down to `[]`
  obtain ⟨hpropC, hpropTr⟩ := desc hpropOK hprc hΓ2 ⟨_, hprT⟩
  obtain ⟨habC, habTr⟩ := desc hasBoolOK habc hΓ2 ⟨_, habT⟩
  obtain ⟨hpfC, hpfTr⟩ := desc hproofOK hpfc hΓ2 ⟨_, hpfT⟩
  obtain ⟨htoDecC, htoDecTr⟩ := desc htoDecOK htd
    (show OnCtx (_ :: _ :: _ :: _) _ from ⟨⟨⟨hΓ2, hI3⟩, hI4⟩, hI5⟩) ⟨_, htdT⟩
  exact ⟨_, _, _, _, hpropTr, habTr, hpfTr, htoDecTr, hpropC, habC, hpfC, htoDecC,
    Condition.check.gadget_types hnat htypeC htoDecC hpropC habC hpfC hT⟩

/-- Taking a checked `Condition.ite` apart: unlike `dite` there are no binders, so this is a
plain spine inversion, and the shape it lands on is `iteApp`.

Stated at an arbitrary `VLCtx` rather than at a `c.withMLC m`: a conditional nested in a `dite`'s
branch is translated under that `dite`'s own binder, and `(none, .vlam P) :: Δ` is not an
`MLCtx`'s context -- every entry of one names an fvar. `Nat.bitwise`'s equation body is three
conditionals deep inside one, so it needs this form. -/
theorem Condition.ite_tr_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {cnd : Condition}
    {α : Expr} {args : Array Expr} {t e : Expr} {r : VExpr}
    (H : TrExprS env Us Δ (cnd.ite α args t e) r) :
    ∃ α' P D t' e',
      TrExprS env Us Δ α α' ∧
      TrExprS env Us Δ (mkAppN cnd.prop args) P ∧
      TrExprS env Us Δ (mkAppN cnd.dec args) D ∧
      TrExprS env Us Δ t t' ∧ TrExprS env Us Δ e e' ∧
      r = iteApp α' P D t' e' := by
  simp only [Condition.ite, mkApp5, mkApp4, mkApp] at H
  cases H with | app _ _ hf he
  cases hf with | app _ _ hf2 ht
  cases hf2 with | app _ _ hf3 hdec
  cases hf3 with | app _ _ hf4 hprop
  cases hf4 with | app _ _ hic hα
  cases hic with | const hci hus hlen
  simp [VLevel.ofLevel] at hus; subst hus
  exact ⟨_, _, _, _, _, hα, hprop, hdec, ht, he, rfl⟩

theorem Condition.ite_tr_inv {c : VContext} {cnd : Condition} {m : MLCtx} [c.MLCWF m]
    {α : Expr} {args : Array Expr} {t e : Expr} {r : VExpr}
    (H : (c.withMLC m).TrExprS (cnd.ite α args t e) r) :
    ∃ α' P D t' e',
      (c.withMLC m).TrExprS α α' ∧
      (c.withMLC m).TrExprS (mkAppN cnd.prop args) P ∧
      (c.withMLC m).TrExprS (mkAppN cnd.dec args) D ∧
      (c.withMLC m).TrExprS t t' ∧ (c.withMLC m).TrExprS e e' ∧
      r = iteApp α' P D t' e' := Condition.ite_tr_inv' H

/-- Inverting a `Condition.dite`'s translation: its four arguments' translations, and the shape
of the whole. `WF_dite` is the other direction -- it *builds* the translation from pieces the
caller has. A caller that got its conditional from `checkType`, as the fuel recursions do, has
the translation and wants the pieces.

At an arbitrary `VLCtx`, for the reason `ite_tr_inv'` is. -/
theorem Condition.dite_tr_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {cnd : Condition}
    {args : Array Expr} {t e : Expr} {r : VExpr}
    (hu : noProj (mkAppN cnd.prop args))
    (H : TrExprS env Us Δ (cnd.dite args t e) r) :
    ∃ P D t' e',
      TrExprS env Us Δ (mkAppN cnd.prop args) P ∧
      TrExprS env Us Δ (mkAppN cnd.dec args) D ∧
      TrExprS env Us ((none, .vlam P) :: Δ) t t' ∧
      TrExprS env Us ((none, .vlam (vexpr(Not).app P)) :: Δ) e e' ∧
      r = diteApp P D (.lam P t') (.lam (vexpr(Not).app P) e') := by
  simp only [Condition.dite, Expr.lam0, mkApp4, mkApp] at H
  cases H with | app _ _ hf helam
  cases hf with | app _ _ hf2 htlam
  cases hf2 with | app _ _ hf3 hdec
  cases hf3 with | app _ _ hdc hprop
  -- the head, `@dite Nat`
  cases hdc with | app _ _ hdc1 hdnat
  cases hdc1 with | const hci hus hlen
  simp [VLevel.ofLevel] at hus; subst hus
  obtain ⟨rfl, -⟩ := hdnat.const0_inv (Us' := Us) (Δ' := Δ)
  -- the two branches, and their binder types
  cases htlam with | lam _ hty ht
  cases helam with | lam _ hnty he
  cases TrExprS.unique (noProj.isUnique hu) hty hprop
  cases hnty with | app _ _ hnc hnp
  cases TrExprS.unique (noProj.isUnique hu) hnp hprop
  obtain ⟨rfl, -⟩ := hnc.const0_inv (Us' := Us) (Δ' := Δ)
  exact ⟨_, _, _, _, hprop, hdec, ht, he, rfl⟩

theorem Condition.dite_tr_inv {c : VContext} {cnd : Condition} {m : MLCtx} [c.MLCWF m]
    {args : Array Expr} {t e : Expr} {r : VExpr}
    (hu : noProj (mkAppN cnd.prop args))
    (H : (c.withMLC m).TrExprS (cnd.dite args t e) r) :
    ∃ P D t' e',
      (c.withMLC m).TrExprS (mkAppN cnd.prop args) P ∧
      (c.withMLC m).TrExprS (mkAppN cnd.dec args) D ∧
      TrExprS c.venv c.lparams ((none, .vlam P) :: (c.withMLC m).vlctx) t t' ∧
      TrExprS c.venv c.lparams
        ((none, .vlam (vexpr(Not).app P)) :: (c.withMLC m).vlctx) e e' ∧
      r = diteApp P D (.lam P t') (.lam (vexpr(Not).app P) e') :=
  Condition.dite_tr_inv' hu H

/-! What a conditional mentions: its arguments and its branches, the rest being closed. This is
the side condition `checkType` asks of every equation body a recognizer builds. -/

theorem Condition.fvarsIn_ite {P : FVarId → Prop} {cnd : Condition} [hOK : cnd.OK]
    {α : Expr} {args : Array Expr} {t e : Expr} (hα : FVarsIn P α)
    (hargs : ∀ a ∈ args.toList, FVarsIn P a) (ht : FVarsIn P t) (he : FVarsIn P e) :
    FVarsIn P (cnd.ite α args t e) := by
  have hp : FVarsIn P (mkAppN cnd.prop args) := by
    rw [Expr.mkAppN_eq]; exact FVarsIn.appN (CondOK.fvarsIn hOK.prop) hargs
  have hd : FVarsIn P (mkAppN cnd.dec args) := by
    rw [Expr.mkAppN_eq]; exact FVarsIn.appN (CondOK.fvarsIn hOK.dec) hargs
  exact ⟨⟨⟨⟨⟨by simp [FVarsIn, Level.hasMVar'], hα⟩, hp⟩, hd⟩, ht⟩, he⟩

theorem Condition.fvarsIn_dite {P : FVarId → Prop} {cnd : Condition} [hOK : cnd.OK]
    {args : Array Expr} {t e : Expr}
    (hargs : ∀ a ∈ args.toList, FVarsIn P a) (ht : FVarsIn P t) (he : FVarsIn P e) :
    FVarsIn P (cnd.dite args t e) := by
  have hp : FVarsIn P (mkAppN cnd.prop args) := by
    rw [Expr.mkAppN_eq]; exact FVarsIn.appN (CondOK.fvarsIn hOK.prop) hargs
  have hd : FVarsIn P (mkAppN cnd.dec args) := by
    rw [Expr.mkAppN_eq]; exact FVarsIn.appN (CondOK.fvarsIn hOK.dec) hargs
  exact ⟨⟨⟨⟨by simp [FVarsIn, Level.hasMVar'], hp⟩, hd⟩, hp, ht⟩, ⟨by simp [FVarsIn], hp⟩, he⟩

/-- `Condition.decide` is `ite` at `Bool` with the two boolean literals as branches, so taking
one apart is `ite_tr_inv'` plus the branches, which translate the one way they can. The type
argument is left as it comes: nothing in the model pins `Bool`'s translation, and a
`reflectNatNat` condition's `IteEval` is generic in it. -/
theorem Condition.decide_tr_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {cnd : Condition}
    {args : Array Expr} {r : VExpr} (hprim : env.HasPrimitives) (hbool : env.contains ``Bool)
    (H : TrExprS env Us Δ (cnd.decide args) r) :
    ∃ α' P D, TrExprS env Us Δ (mkAppN cnd.prop args) P ∧
      TrExprS env Us Δ (mkAppN cnd.dec args) D ∧
      r = iteApp α' P D (.boolLit true) (.boolLit false) := by
  obtain ⟨_, _, _, _, _, -, hP, hD, ht, he, rfl⟩ := Condition.ite_tr_inv' H
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) ht (TrExprS.boolLit hprim hbool true).1
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) he (TrExprS.boolLit hprim hbool false).1
  exact ⟨_, _, _, hP, hD, rfl⟩

/-- What a closed-off use of `natEq` has to say about its two arguments: they are `Nat`s, and the
decision at them is the literals' `Nat.beq`. The arguments are only *worth* literals -- a
recognizer reaches them through a closing, which computes rather than substitutes a literal in --
so both are read off their equations. -/
theorem Condition.WF.natEq_args {c : VContext} (w : Condition.WF c Condition.natEq)
    (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat) (E : c.Ext)
    {A B : VExpr} {x y : Nat} (hA : E.IsDefEqU₀ A (.natLit x)) (hB : E.IsDefEqU₀ B (.natLit y)) :
    List.Forall₂ (E.venv.HasType c.lparams.length []) [A, B] Condition.natEq.impl.domain ∧
      E.IsDefEqU₀ (w.himpl.asBool'.appN [A, B]) (.boolLit (Nat.beq x y)) := by
  have hT : ∀ {v : VExpr} {k : Nat}, E.IsDefEqU₀ v (.natLit k) → E.HasType₀ v .nat := fun h =>
    VEnv.HasType.defeqU_l E.wf trivial h.symm (E.monoT (hprim.natLitT c.Ewf hnat _ []))
  have hlit := w.natEq_apply₀ hprim E x y rfl
  have hwfl : E.WF₀ (w.himpl.asBool'.appN [.natLit x, .natLit y]) :=
    ⟨_, hlit.choose_spec.hasType.1⟩
  have hhd := VExpr.WF.appN_inv E.wf trivial hwfl
  refine ⟨.cons (hT hA) (.cons (hT hB) .nil), .trans E.wf trivial (.symm ?_) hlit⟩
  exact VEnv.IsDefEqU.appN' E.wf trivial (xs := [VExpr.natLit x, VExpr.natLit y]) (ys := [A, B])
    ⟨_, hhd.choose_spec⟩ (.cons hA.symm (.cons hB.symm .nil)) hwfl

/-- `natEq`'s conditional at arguments that are worth literals: the branch `Nat.beq` selects. -/
theorem Condition.WF.natEq_iteEval {c : VContext} {w : Condition.WF c Condition.natEq}
    (hite : w.IteEval) (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat)
    (E : c.Ext) {A B α' t' e' : VExpr} {x y : Nat}
    (hA : E.IsDefEqU₀ A (.natLit x)) (hB : E.IsDefEqU₀ B (.natLit y))
    (hwf : E.WF₀ (iteApp α' ((w.prop'.app A).app B) ((w.dec'.app A).app B) t' e')) :
    E.IsDefEqU₀ (iteApp α' ((w.prop'.app A).app B) ((w.dec'.app A).app B) t' e')
      (if Nat.beq x y then t' else e') := by
  obtain ⟨hargs, hbe⟩ := w.natEq_args hprim hnat E hA hB
  have h := hite E (args' := [A, B]) (Nat.beq x y) nofun trivial hargs rfl hbe
    (by simpa [VExpr.appN] using hwf)
  simpa [VExpr.appN] using h

/-- The same for the `dite` form, whose branches take the decision's proof. -/
theorem Condition.WF.natEq_diteEval {c : VContext} {w : Condition.WF c Condition.natEq}
    (hdite : w.DiteEval) (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat)
    (E : c.Ext) {A B t' e' : VExpr} {x y : Nat}
    (hA : E.IsDefEqU₀ A (.natLit x)) (hB : E.IsDefEqU₀ B (.natLit y))
    (hwf : E.WF₀ (diteApp ((w.prop'.app A).app B) ((w.dec'.app A).app B) t' e')) :
    ∃ pf, E.IsDefEqU₀ (diteApp ((w.prop'.app A).app B) ((w.dec'.app A).app B) t' e')
      (if Nat.beq x y then t'.app pf else e'.app pf) := by
  obtain ⟨hargs, hbe⟩ := w.natEq_args hprim hnat E hA hB
  have h := hdite E (args' := [A, B]) (Nat.beq x y) trivial hargs rfl hbe
    (by simpa [VExpr.appN] using hwf)
  simpa [VExpr.appN] using h

/-- `natEq.decide` at two arguments that are worth literals, closed off: the whole gadget is
worth their `Nat.beq`. The arguments' values are asked for at any translation of them, so that
this composes with `natBinLitTr` -- `Nat.bitwise` decides on `n % 2 = 1`, whose left side is
itself a reflected primitive at a probe variable. -/
theorem Condition.WF.natEq_decideTr {c : VContext} {w : Condition.WF c Condition.natEq}
    (hite : w.IteEval) (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat)
    (hbool : c.venv.contains ``Bool) (E : c.Ext) {Δ : VLCtx} {σ : VExpr.Subst}
    {A B : Expr} {r : VExpr} (x y : Nat) (hnpA : noProj A) (hnpB : noProj B)
    (hA : ∀ {A' : VExpr}, TrExprS c.venv c.lparams Δ A A' → E.WF₀ (A'.subst σ) →
      E.IsDefEqU₀ (A'.subst σ) (.natLit x))
    (hB : ∀ {B' : VExpr}, TrExprS c.venv c.lparams Δ B B' → E.WF₀ (B'.subst σ) →
      E.IsDefEqU₀ (B'.subst σ) (.natLit y))
    (hr : TrExprS c.venv c.lparams Δ (Condition.natEq.decide #[A, B]) r)
    (hwf : E.WF₀ (r.subst σ)) : E.IsDefEqU₀ (r.subst σ) (.boolLit (Nat.beq x y)) := by
  obtain ⟨_, _, _, hP, hD, rfl⟩ := Condition.decide_tr_inv' hprim hbool hr
  obtain ⟨_, _, hA2, hB2, rfl⟩ := w.prop_app2_inv hP
  obtain ⟨_, _, hA3, hB3, rfl⟩ := w.dec_app2_inv hD
  cases TrExprS.unique (noProj.isUnique hnpA) hA3 hA2
  cases TrExprS.unique (noProj.isUnique hnpB) hB3 hB2
  simp only [iteApp, VExpr.subst, w.propC.subst_eq', w.decC.subst_eq', VExpr.subst_boolLit] at hwf ⊢
  have pk {f a : VExpr} (h : E.WF₀ (f.app a)) : E.WF₀ f ∧ E.WF₀ a :=
    h.app_inv₂ E.wf trivial
  have hwfP := (pk (pk (pk (pk hwf).1).1).1).2
  refine .trans E.wf trivial (w.natEq_iteEval hite hprim hnat E
    (hA hA2 (pk (pk hwfP).1).2) (hB hB2 (pk hwfP).2) hwf) ?_
  rw [show (if Nat.beq x y then VExpr.boolLit true else .boolLit false)
    = .boolLit (Nat.beq x y) from by cases Nat.beq x y <;> simp]
  exact ⟨_, E.monoT (TrExprS.boolLit (Us := c.lparams) (Δ := ([] : VLCtx))
    hprim hbool (Nat.beq x y)).2⟩

/-- The `dite` equation as a fact about `VExpr`s: a conditional built from the condition's own
`prop` and `dec` collapses to the branch the decision selects. This is the content of `WF_dite`
without the `Expr`-level packaging, and it is what `Condition.WF.DiteEval` is proved from. -/
theorem Condition.WF.reflect_diteEval {c : VContext} (E : c.Ext)
    {prop' dec' asBool' proof' toDec' : VExpr} {reflect : Reflection} (w : Reflection.WF c reflect)
    (hWD : w.WF_dite toDec') (hDT : w.DITE_T toDec')
    (htypeTΓ : ∀ {Γ}, E.venv.HasType c.lparams.length Γ w.type' vexpr(Prop → Bool → Prop))
    (H : ∀ ⦃Γ⦄, OnCtx Γ (E.venv.IsType c.lparams.length) →
      ∀ {x y : VExpr}, E.venv.HasType c.lparams.length Γ x .nat →
      E.venv.HasType c.lparams.length Γ y .nat →
      E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) (.sort .zero) ∧
      E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
      E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
        ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
      E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
          ((proof'.app x).app y)))
    ⦃Γ⦄ {x y t' e' : VExpr} (b : Bool)
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hxT : E.venv.HasType c.lparams.length Γ x .nat)
    (hyT : E.venv.HasType c.lparams.length Γ y .nat)
    (hbb : E.venv.IsDefEqU c.lparams.length Γ ((asBool'.app x).app y) (.boolLit b))
    (hwf : VExpr.WF E.venv c.lparams.length Γ
      (diteApp ((prop'.app x).app y) ((dec'.app x).app y) t' e')) :
    ∃ pf, E.venv.IsDefEqU c.lparams.length Γ
      (diteApp ((prop'.app x).app y) ((dec'.app x).app y) t' e')
      (if b then t'.app pf else e'.app pf) := by
  obtain ⟨oT, oF, hoTTr, hoFTr, hWDeq⟩ := hWD
  have hToDecT : w.ToDecT toDec' := hDT.toDecT
  have ⟨hpT, hblT, hHT, hdecEq⟩ := H hΓ hxT hyT
  -- the evidence, retyped at the literal the decision evaluates to
  have hHT' : E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
      ((w.type'.app ((prop'.app x).app y)).app (.boolLit b)) :=
    VEnv.HasType.defeqU_r E.wf hΓ
      (VEnv.IsDefEqU.app_arg E.wf hΓ (.app htypeTΓ hpT) hblT hbb) hHT
  -- the decision procedure is `toDec` at that literal
  obtain ⟨_, _, _, _, _, _, -, ⟨htd2, hb2⟩, -⟩ := hToDecT.spine E hΓ hpT hblT hHT
  have hdecEq' : E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
      (((toDec'.app ((prop'.app x).app y)).app (.boolLit b)).app ((proof'.app x).app y)) := by
    refine hdecEq.trans E.wf hΓ ?_
    exact .appN E.wf hΓ (vs := [(proof'.app x).app y])
      (.app_arg E.wf hΓ htd2 hb2 hbb) (hToDecT E hΓ hpT hblT hHT)
  have hblitT := hblT.defeqU_l E.wf hΓ hbb
  have hd3 := hDT E hΓ hpT hblitT hHT'
  obtain ⟨A₀, B₀, hf₀, ha₀⟩ := hd3.app_inv E.wf hΓ
  have ha₀' := ha₀.defeqU_l E.wf hΓ hdecEq'.symm
  -- the branches' types come from the conditional's own well-formedness, matched against the
  -- `dite` gadget's: its fourth and fifth domains are `p → Nat` and `¬p → Nat`
  have hd3' := hd3.defeqU_l E.wf hΓ (.app_arg E.wf hΓ hf₀ ha₀ hdecEq'.symm)
  obtain ⟨_, _, hwf1, heT0⟩ := VExpr.WF.app_inv E.wf hΓ hwf
  obtain ⟨_, _, hwf2, htT0⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hwf1⟩
  obtain ⟨⟨_, hdom4⟩, -⟩ := (hwf2.uniqU E.wf hΓ hd3').forallE_inv E.wf hΓ
  have htT := htT0.defeqU_r E.wf hΓ ⟨_, hdom4⟩
  obtain ⟨⟨_, hdom5⟩, -⟩ :=
    (hwf1.uniqU E.wf hΓ (VEnv.HasType.app hd3' htT)).forallE_inv E.wf hΓ
  have heT := heT0.defeqU_r E.wf hΓ ⟨_, hdom5⟩
  have hval := hWDeq E b hΓ hpT hHT' htT (by simpa [VExpr.inst, VExpr.inst_lift] using heT)
  have hd3' := hd3.defeqU_l E.wf hΓ (.app_arg E.wf hΓ hf₀ ha₀ hdecEq'.symm)
  have hcong : E.venv.IsDefEqU c.lparams.length Γ
      (diteApp ((prop'.app x).app y) ((dec'.app x).app y) t' e')
      (diteApp ((prop'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app (.boolLit b)).app ((proof'.app x).app y))
        t' e') := by
    refine .appN E.wf hΓ (vs := [t', e']) (.app_arg E.wf hΓ hf₀ ha₀' hdecEq') ?_
    refine ⟨_, (hd3'.app htT).app ?_⟩
    simpa [VExpr.inst, VExpr.inst_lift] using heT
  refine ⟨if b then (oT.app ((prop'.app x).app y)).app ((proof'.app x).app y)
    else (oF.app ((prop'.app x).app y)).app ((proof'.app x).app y),
    VEnv.IsDefEqU.trans E.wf hΓ hcong ?_⟩
  cases hfab : b <;> simpa [hfab] using hval

/-- The `ite` equation as a fact about `VExpr`s, the counterpart of `reflect_diteEval`. -/
theorem Condition.WF.reflect_iteEval {c : VContext} (E : c.Ext)
    {prop' dec' asBool' proof' toDec' : VExpr} {reflect : Reflection} (w : Reflection.WF c reflect)
    (hWI : w.WF_ite toDec') (hIT : w.ITE_T toDec')
    (htypeTΓ : ∀ {Γ}, E.venv.HasType c.lparams.length Γ w.type' vexpr(Prop → Bool → Prop))
    (H : ∀ ⦃Γ⦄, OnCtx Γ (E.venv.IsType c.lparams.length) →
      ∀ {x y : VExpr}, E.venv.HasType c.lparams.length Γ x .nat →
      E.venv.HasType c.lparams.length Γ y .nat →
      E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) vexpr(Prop) ∧
      E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
      E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
        ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
      E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
          ((proof'.app x).app y)))
    ⦃Γ⦄ {x y α' t' e' : VExpr} (b : Bool)
    (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
    (hxT : E.venv.HasType c.lparams.length Γ x .nat)
    (hyT : E.venv.HasType c.lparams.length Γ y .nat)
    (hbb : E.venv.IsDefEqU c.lparams.length Γ ((asBool'.app x).app y) (.boolLit b))
    (hwf : VExpr.WF E.venv c.lparams.length Γ
        (iteApp α' ((prop'.app x).app y) ((dec'.app x).app y) t' e')) :
    E.venv.IsDefEqU c.lparams.length Γ
      (iteApp α' ((prop'.app x).app y) ((dec'.app x).app y) t' e')
      (if b then t' else e') := by
  have hToDecT : w.ToDecT toDec' := hIT.toDecT
  have ⟨hpT, hblT, hHT, hdecEq⟩ := H hΓ hxT hyT
  -- the type argument really is a `Type`. Nothing pins the sort `Nat` lives in, but `ite`'s own
  -- first domain is pinned -- by the gadget, which `checkITE` compares against `∀ α : Type` --
  -- and the conditional being well formed types its type argument there
  have hαT : E.venv.HasType c.lparams.length Γ α' vexpr(Type) :=
    have hprop0 : E.venv.HasType c.lparams.length Γ vexpr(Prop) vexpr(Type) := .sort trivial
    have ⟨_, _, hf1, _⟩ := VExpr.WF.app_inv E.wf hΓ hwf
    have ⟨_, _, hf2, _⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf1⟩
    have ⟨_, _, hf3, _⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf2⟩
    have ⟨_, _, hf4, _⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf3⟩
    have ⟨_, _, hite0, hα0⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf4⟩
    have ⟨_, _, hg1, _⟩ := VExpr.WF.app_inv E.wf hΓ
      ⟨_, hIT E hΓ hpT hblT hHT hprop0⟩
    have ⟨_, _, hg1', _⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hg1⟩
    have ⟨_, _, hg2, hs0⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hg1'⟩
    have ⟨⟨_, hdom⟩, _⟩ := (hite0.uniqU E.wf hΓ hg2).forallE_inv E.wf hΓ
    .defeqU_r E.wf hΓ (hs0.uniqU E.wf hΓ hprop0) (.defeqU_r E.wf hΓ ⟨_, hdom⟩ hα0)
  -- the evidence, retyped at the literal the decision evaluates to
  have hHT' : E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
      ((w.type'.app ((prop'.app x).app y)).app (.boolLit b)) :=
    .defeqU_r E.wf hΓ (.app_arg E.wf hΓ (.app htypeTΓ hpT) hblT hbb) hHT
  -- the decision procedure is `toDec` at that literal
  obtain ⟨_, _, _, _, _, _, -, ⟨htd2, hb2⟩, -⟩ := hToDecT.spine E hΓ hpT hblT hHT
  have hdecEq' : E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
      (((toDec'.app ((prop'.app x).app y)).app (.boolLit b)).app ((proof'.app x).app y)) :=
    hdecEq.trans E.wf hΓ <|
    (hbb.app_arg E.wf hΓ htd2 hb2).appN E.wf hΓ (vs := [_]) (hToDecT E hΓ hpT hblT hHT)
  have hblitT : E.venv.HasType c.lparams.length Γ (.boolLit b) .bool :=
    hblT.defeqU_l E.wf hΓ hbb
  have hi3 := hIT E hΓ hpT hblitT hHT' hαT
  obtain ⟨A₀, B₀, hf₀, ha₀⟩ := hi3.app_inv E.wf hΓ
  have ha₀' := ha₀.defeqU_l E.wf hΓ hdecEq'.symm
  have hi3' := hi3.defeqU_l E.wf hΓ (hdecEq'.symm.app_arg E.wf hΓ hf₀ ha₀)
  -- the branches' types come from the conditional's own well-formedness, matched against the
  -- `ite` gadget's: both its fourth and fifth domains are the type argument
  obtain ⟨_, _, hwf1, heT0⟩ := VExpr.WF.app_inv E.wf hΓ hwf
  obtain ⟨_, _, hwf2, htT0⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hwf1⟩
  obtain ⟨⟨_, hdom4⟩, -⟩ := (hwf2.uniqU E.wf hΓ hi3').forallE_inv E.wf hΓ
  have htT := htT0.defeqU_r E.wf hΓ ⟨_, hdom4⟩
  obtain ⟨⟨_, hdom5⟩, -⟩ := (hwf1.uniqU E.wf hΓ (hi3'.app htT)).forallE_inv E.wf hΓ
  have heT := heT0.defeqU_r E.wf hΓ ⟨_, hdom5⟩
  have heT' : E.venv.HasType c.lparams.length Γ e' α' := by simpa [VExpr.inst_lift] using heT
  have hval := hWI E b hΓ hpT hHT' hαT htT heT'
  have hcong : E.venv.IsDefEqU c.lparams.length Γ
      (iteApp α' ((prop'.app x).app y) ((dec'.app x).app y) t' e')
      (iteApp α' ((prop'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app (.boolLit b)).app ((proof'.app x).app y))
        t' e') := by
    refine .appN E.wf hΓ (vs := [t', e']) (.app_arg E.wf hΓ hf₀ ha₀' hdecEq') ?_
    exact ⟨_, VEnv.HasType.app (VEnv.HasType.app hi3' htT) heT⟩
  exact .trans E.wf hΓ hcong hval

/-- `Condition.WF.WF_ite` for a `reflectNatNat`, from the reflection's own `WF_ite`. The
consumer's conditional decides by `dec` applied to the arguments, the reflection's by `toDec` at
the proposition, the boolean and the evidence; `e ≡ dec` is what joins them, and the rest is
reading the three pieces' arities off the checks. -/
theorem Condition.WF.reflect_ite {c : VContext} {prop dec asBool proof : Expr}
    {reflect : Reflection} {prop' dec' asBool' proof' toDec' : VExpr}
    (w : Reflection.WF c reflect)
    (w' : Condition.WF c ⟨prop, dec, .reflectNatNat asBool reflect proof⟩)
    (hw'prop : w'.prop' = prop') (hw'dec : w'.dec' = dec')
    (hIT : w.ITE_T toDec')
    (hpropTrΓ : ∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ prop prop')
    (hdecTrΓ : ∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ dec dec')
    (H : ∀ (E : c.Ext) ⦃Γ : List VExpr⦄, OnCtx Γ (E.venv.IsType c.lparams.length) →
      ∀ {x y : VExpr}, E.venv.HasType c.lparams.length Γ x .nat →
      E.venv.HasType c.lparams.length Γ y .nat →
      E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) (.sort .zero) ∧
      E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
      E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
        ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
      E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
        (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
          ((proof'.app x).app y))) :
    w'.WF_ite (natOnly := false) := by
  intro m cwfm α t e args α' t' e' args' hα hαT _ hargs hargsT ht htT he heT
  have hΓm := (c.withMLC m).Δwf.toCtx
  have hαT' := hαT rfl
  let .cons (a := x) hxT (.cons (a := y) hyT .nil) := hargsT
  -- the condition, the decision and the evidence at those arguments
  have ⟨hpT, hblT, hHT, hdecEq⟩ := H c.self hΓm hxT hyT
  -- the decision procedure at those arguments decides the condition
  have hToDecT : w.ToDecT toDec' := hIT.toDecT
  obtain ⟨_, htdT⟩ := hToDecT c.self hΓm hpT hblT hHT
  have hdecT : VExpr.WF c.venv c.lparams.length (c.withMLC m).vlctx.toCtx
      ((dec'.app x).app y) := ⟨_, VEnv.HasType.defeqU_l c.Ewf hΓm hdecEq.symm htdT⟩
  -- the conditional at the reflection's decision, then at the condition's own
  have hiteT := hIT c.self hΓm hpT hblT hHT hαT'
  obtain ⟨A₀, B₀, hf₀, ha₀⟩ := hiteT.app_inv c.Ewf.orderedStrong hΓm
  have hiteT' : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx
      (((vexpr(@ite.{1}).app α').app ((prop'.app x).app y)).app ((dec'.app x).app y))
      (.forallE α' (.forallE α'.lift α'.lift.lift)) :=
    hiteT.defeqU_l c.Ewf hΓm (hdecEq.symm.app_arg c.Ewf hΓm hf₀ ha₀)
  have hiteT2 := hiteT'.app htT
  have heT2 : c.venv.HasType c.lparams.length (c.withMLC m).vlctx.toCtx e' α' := heT
  have hiteT3 := hiteT2.app (by rw [VExpr.inst_lift]; exact heT2)
  -- the source arguments, and the pieces' translations at them
  generalize hal : args.toList = al at hargs
  obtain ⟨xs, ys, rfl, hxTr, hyTr⟩ : ∃ xs ys, al = [xs, ys] ∧
      (c.withMLC m).TrExprS xs x ∧ (c.withMLC m).TrExprS ys y := by
    cases hargs with | cons h1 h2; cases h2 with | cons h3 h4; cases h4; exact ⟨_, _, rfl, h1, h3⟩
  have hpropApp : (c.withMLC m).TrExprS (prop.appN [xs, ys]) ((prop'.app x).app y) :=
    TrExprS.appN c.Ewf.orderedStrong hΓm hpropTrΓ (.cons hxTr (.cons hyTr .nil)) ⟨_, hpT⟩
  have hdecApp : (c.withMLC m).TrExprS (dec.appN [xs, ys]) ((dec'.app x).app y) :=
    TrExprS.appN c.Ewf.orderedStrong hΓm hdecTrΓ (.cons hxTr (.cons hyTr .nil)) hdecT
  -- `ite` itself translates, since the conditional it heads is well typed
  obtain ⟨_, _, hf₁, -⟩ := hf₀.app_inv c.Ewf.orderedStrong hΓm
  obtain ⟨_, _, hf₂, -⟩ := hf₁.app_inv c.Ewf.orderedStrong hΓm
  obtain ⟨ci, hci, -, hlen⟩ := hf₂.const_inv c.Ewf.orderedStrong hΓm
  have hiteCTr : (c.withMLC m).TrExprS q(@ite.{1}) vexpr(@ite.{1}) := .const hci rfl hlen
  simp only [Condition.ite, Expr.mkAppN_eq, hal, mkApp5, mkApp4, mkApp, mkAppB, Expr.appN,
    iteApp, VExpr.appN, hw'prop, hw'dec]
  exact TrExprS.appN c.Ewf.orderedStrong hΓm hiteCTr
    (.cons hα (.cons hpropApp (.cons hdecApp (.cons ht (.cons he .nil))))) ⟨_, hiteT3⟩

/-- Verification boundary for `Condition.check`. The flags select which of the three parts
hold, exactly as they select which checks run; `Condition.bool` at `dite := true` throws, so
that case is vacuous rather than excluded. `natOnly` follows the `impl` because the `.bool`
branch only ever builds and compares `ite` at `Nat`, while a `reflectNatNat`'s `checkITE`
covers every `α : Type`. -/
theorem Condition.check.WF {c : VContext} {s : VState} {cond : Condition}
    {fail : ∀ {α}, M α} {ite dite : Bool}
    (hnat : c.venv.contains ``Nat) (hbool : c.venv.contains ``Bool) [hok : cond.OK]
    -- the check runs before any binder, which is what makes its results usable at the arbitrary
    -- `MLCtx` of `WF_ite`: a fact proved at `[]` transports to every context (`TrTerm.of_nil'`),
    -- while one proved at some `c.vlctx` transports to nothing, the two being unrelated
    (hnil : c.vlctx = [])
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (cond.check fail ite dite).WF c s fun _ _ =>
      ∃ w : Condition.WF c cond,
        (ite → w.WF_ite (natOnly := cond.impl matches .bool) ∧
          w.IteEval (natOnly := cond.impl matches .bool)) ∧
        (dite → w.WF_dite ∧ w.DiteEval ∧ w.DecT) := by
  obtain ⟨prop, dec, impl⟩ := cond
  have hnil' : c.vlctx.toCtx = [] := by rw [hnil]; rfl
  -- `fail` never returns, so a `fail` in front of a continuation proves whatever the continuation
  -- was supposed to: this is the shape every `unless` in the check has.
  have hfailb {α β} {k : α → M β} {c s Q} : (fail >>= k).WF c s Q :=
    .bind (hfail (Q := fun _ _ => False)) fun _ _ _ h => h.elim
  unfold Condition.check
  refine .bind (checkType.WF (CondOK.fvarsIn hok.dec))
    fun _ _ _ ⟨dec', decTy', _, hdecTr, _, hdecT⟩ => ?_
  cases impl with
  | bool =>
    dsimp only
    refine .bind (checkType.WF (CondOK.fvarsIn hok.prop))
      fun _ _ _ ⟨prop', propTy', _, hpropTr, hpropTyTr, hpropT⟩ => ?_
    refine .bind (isDefEq.WF hpropTyTr
      (TrExprS.boolProp c.Ewf c.hasPrimitives hbool c.Δwf.toCtx)) fun _ _ _ hbp => ?_
    split <;> [rename_i hbp1; exact hfailb]
    -- the predicate's type is `Bool → Prop` on the nose
    have hpropT' : c.venv.HasType c.lparams.length [] prop' (.forallE .bool (.sort .zero)) := by
      rw [← hnil']
      exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hbp hbp1) hpropT
    -- a `[]`-level fact is a fact at `c`, since the check runs before any binder
    have atC {e A} (h : c.venv.HasType c.lparams.length [] e A) :
        c.venv.HasType c.lparams.length c.vlctx.toCtx e A := by rw [hnil']; exact h
    have hnatT Γ (h : OnCtx Γ (c.venv.IsType c.lparams.length)) :
        c.venv.IsType c.lparams.length Γ .nat := c.hasPrimitives.natIsType' c.Ewf hnat h
    let w : Condition.WF c ⟨prop, dec, .bool⟩ := {
      prop', dec', himpl := (), hprop := hpropTr, hdec := hdecTr, vnil := hnil
      propT := by
        intro E Γ _ args hargs
        cases hargs with | cons hb hrest
        cases hrest
        simpa [VExpr.appN, VExpr.inst] using
          (VEnv.HasType.weak0 E.wf (E.monoT hpropT')).app (by simpa using hb) }
    split
    · -- `ite = true`: the conditional is built at both branches and compared to each
      rename_i hite1
      refine .bind (checkType.WF ?_)
        fun _ _ _ ⟨nite', niteTy', _, hniteTr, hniteTyTr, hniteT⟩ => ?_
      · simp only [Expr.lam0, mkApp2, mkApp, FVarsIn]
        refine ⟨?_, ⟨⟨?_, ?_⟩, CondOK.fvarsIn hok.prop, ?_⟩, CondOK.fvarsIn hok.dec, ?_⟩ <;>
          simp [Level.hasMVar']
      refine .bind (isDefEq.WF hniteTyTr
        (TrExprS.boolNat3 c.Ewf c.hasPrimitives hnat hbool c.Δwf.toCtx))
        fun _ _ _ hn3 => ?_
      split <;> [rename_i hn31; exact hfailb]
      -- the conditional is `Bool → Nat → Nat → Nat`, which is what types its two applications
      have hniteT' : c.venv.HasType c.lparams.length [] nite'
          (.forallE .bool (.forallE .nat (.forallE .nat .nat))) := by
        rw [← hnil']
        exact VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx (hn3 hn31) hniteT
      have hlit b := show c.TrExprS (.const (if b then ``true else ``false) []) _ ∧
          c.HasType (.boolLit b) .bool by
        have h := TrExprS.boolLit (Us := c.lparams) (Δ := c.vlctx) c.hasPrimitives hbool b
        cases b <;> exact h
      refine .bind (isDefEq.WF (.app (atC hniteT') (hlit true).2 hniteTr (hlit true).1)
        (TrExprS.natProj c.Ewf c.hasPrimitives hnat c.Δwf.toCtx (.inr rfl)).1)
        fun _ _ _ htt => ?_
      split <;> [rename_i htt1; exact hfailb]
      refine .bind (isDefEq.WF (.app (atC hniteT') (hlit false).2 hniteTr (hlit false).1)
        (TrExprS.natProj c.Ewf c.hasPrimitives hnat c.Δwf.toCtx (.inl rfl)).1)
        fun _ _ _ hff => ?_
      split <;> [rename_i hff1; exact hfailb]
      -- The gadget's own shape, read off its translation before any binder. Everything in it is
      -- closed and projection-free -- `prop` and `dec` by `Condition.OK`, the argument a `bvar` --
      -- so every piece is pinned, and `nite'` being *this* term is a syntactic fact. That is what
      -- makes the two halves below the same statement: an `iteApp` built out of the condition's
      -- own pieces *is* the checked gadget applied, so it can be evaluated in whatever context it
      -- has since been carried to rather than only in the one it was built in.
      have huniq {x : Expr} {u : VExpr} {Δ : VLCtx} {v : VExpr} (hx : CondOK x)
          (hu : c.TrExprS x u) (hv : TrExprS c.venv c.lparams Δ x v) : v = u :=
        TrExprS.of_nil_unique c.Ewf (CondOK.noProj hx) (by rw [← hnil]; exact hu) hv
      have hshape : nite' = .lam .bool
          ((vexpr(@_root_.ite Nat).app (prop'.app (.bvar 0))).app (dec'.app (.bvar 0))) := by
        cases hniteTr with | lam _ hty hbody
        cases (hty.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)).1
        let .app _ _ (.app _ _ hite2 hnat2) hdec2 := hbody
        let .app _ _ hiteC hnatC := hite2
        let .app _ _ hp hbv := hnat2
        let .app _ _ hd hbv2 := hdec2
        cases (hnatC.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)).1
        cases huniq hok.prop hpropTr hp
        cases huniq hok.dec hdecTr hd
        cases hiteC with | const h1 h2 h3
        cases hbv with | bvar h
        cases hbv2 with | bvar h'
        simp [VLCtx.find?] at h h'
        obtain ⟨rfl, -⟩ := h; obtain ⟨rfl, -⟩ := h'
        simp [VLevel.ofLevel] at h2
        cases h2; rfl
      have hpropC : prop'.ClosedN := (hpropT'.closedN' c.Ewf.ordered.closed trivial).1
      have hdecC : dec'.ClosedN := ((hnil' ▸ hdecT).closedN' c.Ewf.ordered.closed trivial).1
      split; · exact .throw
      refine .pure ⟨w, fun _ => ⟨?_, ?_⟩, fun h => absurd h ‹_›⟩
      intro m cwfm α t e args α' t' e' args' hα _ hαNat hargs hargsT ht htT he heT
      have hΓm := (c.withMLC m).Δwf.toCtx
      -- the pattern's single argument, a `Bool`
      obtain ⟨b', rfl, hbT⟩ : ∃ b', args' = [b'] ∧ (c.withMLC m).HasType b' .bool := by
        cases hargsT with | cons h1 h2; cases h2; exact ⟨_, rfl, h1⟩
      cases hαNat rfl
      cases (hα.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)).1
      simp only [Condition.ite, Expr.mkAppN_eq, mkApp5, mkApp4, mkApp]
      generalize hal : args.toList = al at hargs
      obtain ⟨barg, rfl, hbarg⟩ : ∃ barg, al = [barg] ∧ (c.withMLC m).TrExprS barg b' := by
        cases hargs with | cons h1 h2; cases h2; exact ⟨_, rfl, h1⟩
      simp only [Expr.appN]
      -- the checked conditional, transported to `m` and instantiated at the argument
      have hniteTrM : (c.withMLC m).TrExprS
          ((Expr.const ``Bool []).lam0 (mkApp2 ((Expr.const ``ite [.succ .zero]).app
            (.const ``Nat [])) (mkApp prop (.bvar 0)) (mkApp dec (.bvar 0)))) nite' :=
        TrExprS.of_nil c.Ewf m.noBV cwfm.wf.tr.wf
          (hniteT'.closedN' c.Ewf.ordered.closed trivial).1 (by rw [← hnil]; exact hniteTr)
      have hniteTM : (c.withMLC m).HasType nite'
          (.forallE .bool (.forallE .nat (.forallE .nat .nat))) := hniteT'.weak0 c.Ewf.ordered
      obtain ⟨ty', body', rfl, -, htyTr, hbodyTr⟩ :
          ∃ ty' body', nite' = .lam ty' body' ∧
            c.venv.IsType c.lparams.length (c.withMLC m).vlctx.toCtx ty' ∧
            (c.withMLC m).TrExprS (.const ``Bool []) ty' ∧
            TrExprS c.venv c.lparams ((none, .vlam ty') :: (c.withMLC m).vlctx)
              (mkApp2 ((Expr.const ``ite [.succ .zero]).app (.const ``Nat []))
                (mkApp prop (.bvar 0)) (mkApp dec (.bvar 0))) body' := by
        cases hniteTrM with | lam h1 h2 h3 => exact ⟨_, _, rfl, h1, h2, h3⟩
      cases (htyTr.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)).1
      have hsrc : (mkApp2 ((Expr.const ``ite [.succ .zero]).app (.const ``Nat []))
            (mkApp prop (.bvar 0)) (mkApp dec (.bvar 0))).instantiate1' barg
          = mkApp2 ((Expr.const ``ite [.succ .zero]).app (.const ``Nat []))
            (mkApp prop barg) (mkApp dec barg) := by
        have hp := CondOK.looseBVarRange hok.prop
        have hd := CondOK.looseBVarRange hok.dec
        simp [mkApp2, mkApp, mkAppB, Expr.instantiate1', Expr.instantiate1_eq_self hp,
          Expr.instantiate1_eq_self hd]
      have hinst := hsrc ▸ TrExprS.inst c.Ewf.ordered hbT hbodyTr hbarg
      -- its type, read off the conditional's own: the beta step is what carries it
      have hlamwf : VExpr.WF c.venv c.lparams.length (c.withMLC m).vlctx.toCtx
          (.lam (.const ``Bool []) body') := ⟨_, hniteTM⟩
      obtain ⟨-, B₀, hbodyT⟩ := hlamwf.lam_inv c.Ewf.orderedStrong hΓm
      have hbeta := VEnv.IsDefEq.beta hbodyT hbT
      have hXT := VEnv.HasType.defeqU_l c.Ewf hΓm ⟨_, hbeta⟩
        (VEnv.HasType.app hniteTM hbT)
      have hX1 := VEnv.HasType.app hXT htT
      have hX2 := VEnv.HasType.app hX1 heT
      -- the built conditional *is* the `iteApp` of the condition's own pieces: `hshape` reads the
      -- gadget's body off its translation, and the pieces are closed, so instantiating it at the
      -- argument leaves them alone
      cases by injection hshape
      rw [show iteApp (.const ``Nat []) (w.prop'.appN [b']) (w.dec'.appN [b']) t' e'
          = (((((VExpr.const ``ite [.succ .zero]).app .nat).app (prop'.app (.bvar 0))).app
              (dec'.app (.bvar 0))).inst b' |>.app t').app e' from by
        simp [w, iteApp, VExpr.appN, VExpr.inst, hpropC.instN_eq, hdecC.instN_eq, VExpr.nat]]
      exact .app hX1 heT (.app hXT htT hinst ht) he
      -- and the same conditional's value, read at whatever context it has been carried to. Only
      -- the gadget's own equations are used, and those were checked before any binder, so nothing
      -- here mentions the context the conditional was built in.
      intro E Γ args' α' t' e' be b hαNat hΓ hargsT happly hbe hwf
      cases hαNat rfl
      cases happly
      have hbT : E.venv.HasType c.lparams.length Γ be .bool := by
        cases hargsT with | cons h1 _ => exact h1
      have hniteTΓ : E.venv.HasType c.lparams.length Γ nite' vexpr(Bool → Nat → Nat → Nat) :=
        (E.monoT hniteT').weak0 E.wf
      -- the gadget at this argument beta-reduces to the head of the caller's conditional
      have hlamwf : VExpr.WF E.venv c.lparams.length Γ
          (.lam .bool
            ((vexpr(@_root_.ite Nat).app (prop'.app (.bvar 0))).app (dec'.app (.bvar 0)))) :=
        ⟨_, by rw [← hshape]; exact hniteTΓ⟩
      obtain ⟨-, B₀, hbodyT⟩ := hlamwf.lam_inv E.wf hΓ
      have hbeta := VEnv.IsDefEq.beta hbodyT hbT
      -- and at a decided argument it is a projection, which the branches then pick from
      have hchk : E.venv.IsDefEqU c.lparams.length Γ (nite'.app (.boolLit b))
          (.lam .nat (.lam .nat (.bvar (if b then 1 else 0)))) := by
        cases b
        · exact .weak0 E.wf (E.mono (hnil' ▸ hff hff1))
        · exact .weak0 E.wf (E.mono (hnil' ▸ htt htt1))
      have hbl : E.venv.HasType c.lparams.length Γ (VExpr.boolLit b) .bool :=
        VEnv.HasType.weak0 E.wf (E.monoT (hnil' ▸ (hlit b).2))
      have hprojT : E.venv.HasType c.lparams.length Γ
          (.lam .nat (.lam .nat (.bvar (if b then 1 else 0)))) vexpr(Nat → Nat → Nat) :=
        VEnv.HasType.defeqU_l E.wf hΓ hchk
          (by simpa [VExpr.inst] using VEnv.HasType.app hniteTΓ hbl)
      -- the head of the conditional is that projection
      have hhead : E.venv.IsDefEqU c.lparams.length Γ
          ((((VExpr.const ``ite [.succ .zero]).app .nat).app (w.prop'.appN [be])).app
            (w.dec'.appN [be]))
          (.lam .nat (.lam .nat (.bvar (if b then 1 else 0)))) := by
        refine .trans E.wf hΓ ?_ (.trans E.wf hΓ
          (.app_arg E.wf hΓ hniteTΓ hbT hbe) hchk)
        rw [show (w.prop'.appN [be] : VExpr) = prop'.app be from rfl,
          show (w.dec'.appN [be] : VExpr) = dec'.app be from rfl, hshape,
          show (((VExpr.const ``ite [.succ .zero]).app .nat).app (prop'.app be)).app (dec'.app be)
            = ((((VExpr.const ``ite [.succ .zero]).app .nat).app (prop'.app (.bvar 0))).app
                (dec'.app (.bvar 0))).inst be from by
            simp [VExpr.inst, hpropC.instN_eq, hdecC.instN_eq, VExpr.nat]]
        exact ⟨_, hbeta.symm⟩
      -- the branches are `Nat`s, since the head they are applied to is
      obtain ⟨A₁, B₁, hf1, heT0⟩ := VExpr.WF.app_inv E.wf hΓ hwf
      obtain ⟨A₀, B₀', hf0, htT0⟩ := VExpr.WF.app_inv E.wf hΓ ⟨_, hf1⟩
      obtain ⟨⟨_, hA0⟩, -⟩ :=
        ((VEnv.HasType.defeqU_l E.wf hΓ hhead hf0).uniqU E.wf hΓ hprojT).forallE_inv E.wf hΓ
      have htT := VEnv.HasType.defeqU_r E.wf hΓ ⟨_, hA0⟩ htT0
      have hf1' := VEnv.HasType.defeqU_l E.wf hΓ
        (VEnv.IsDefEqU.app_fun' E.wf hΓ hhead hf0 htT0) hf1
      obtain ⟨⟨_, hA1⟩, -⟩ :=
        (hf1'.uniqU E.wf hΓ (VEnv.HasType.app hprojT htT)).forallE_inv E.wf hΓ
      have heT := VEnv.HasType.defeqU_r E.wf hΓ ⟨_, hA1⟩ heT0
      refine .trans E.wf hΓ (.appN E.wf hΓ (vs := [t', e']) hhead hwf) ?_
      have hpr := VEnv.IsDefEqU.natProj E.wf hΓ
        (fun _ _ => let ⟨_, hn⟩ := E.monoIsType (hnatT [] trivial)
          ⟨_, VEnv.HasType.weak0 E.wf hn⟩)
        htT heT (i := if b then 1 else 0) (by cases b <;> simp)
      cases b <;> simpa [VExpr.appN] using hpr
    · -- `ite = false`: only the flag-free part of `Condition.WF` is claimed
      rename_i hite0
      split <;> [exact .throw; skip]
      exact .pure ⟨w, fun h => absurd h hite0, fun h => absurd h ‹_›⟩
  | reflectNatNat asBool reflect proof =>
    obtain ⟨hasBoolOK, hproofOK, htypeOK, htoDecOK, hofTrueOK, hofFalseOK, hiteOK, hditeOK⟩ :=
      ConditionImpl.OK.reflect hok.impl
    refine .bind (Reflection.check.WF hbool hnil htypeOK hfail) fun _ _ _ hw => ?_
    obtain ⟨w⟩ := hw
    -- the gadget `e`, and `e ≡ dec`. Between them these are the whole check: the gadget's
    -- translation reads the four pieces -- `toDec` included, which is why no check of its own
    -- is needed -- and its typing types the three the consumer applies.
    refine .bind (checkType.WF ?_) fun _ _ _ ⟨e', eTy', _, heTr, _, heT⟩ => ?_
    · have hp := CondOK.fvarsIn (P := (· ∈ c.vlctx.fvars)) hok.prop
      have ha := CondOK.fvarsIn (P := (· ∈ c.vlctx.fvars)) hasBoolOK
      have hf := CondOK.fvarsIn (P := (· ∈ c.vlctx.fvars)) hproofOK
      have ht := CondOK.fvarsIn (P := (· ∈ c.vlctx.fvars)) htypeOK
      have htd := CondOK.fvarsIn (P := (· ∈ c.vlctx.fvars)) htoDecOK
      simp [Expr.lam0, mkApp3, mkApp2, mkApp, FVarsIn, Level.hasMVar', hp, ha, hf, ht, htd]
    refine .bind (isDefEq.WF heTr hdecTr) fun _ _ _ hed => ?_
    extract_lets F1 F2
    split <;> [rename_i h4; exact hfailb]
    obtain ⟨prop', asBool', proof', toDec', hpropTr, habTr, hpfTr, htoDecTr,
        hpropC, habC, hpfC, htoDecC, hgadget⟩ :=
      Condition.check.gadget_pieces w hnil hnat hok.prop hasBoolOK hproofOK htypeOK htoDecOK
        (by rw [← hnil]; exact heTr) (by rw [← hnil']; exact heT)
    have htoDecTr' : c.TrExprS reflect.toDec toDec' := by
      show TrExprS c.venv c.lparams c.vlctx reflect.toDec toDec'; rw [hnil]; exact htoDecTr
    let +generalize P _ := _
    suffices ∀ {s}, (ite → w.WF_ite toDec' ∧ w.ITE_T toDec') → M.WF c s (F1 ()) P by
      unfold F2; split <;> [skip; exact this (Not.elim ‹_›)]
      exact (Reflection.checkITE.WF w hnil hbool htoDecTr' htoDecC htypeOK htoDecOK hiteOK
        hfail).bind fun _ _ _ h => this fun _ => h
    intro s hI; unfold F1
    suffices ∀ {s}, (dite → w.WF_dite toDec' ∧ w.DITE_T toDec' ∧
        (∀ {Δ : VLCtx}, TrExprS c.venv c.lparams Δ (.const ``Not []) (.const ``Not [])) ∧
        (∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ (.const ``Not [])
          (.forallE (.sort .zero) (.sort .zero)))) → P () s by
      split <;> [skip; exact .pure <| this (s := s) (Not.elim ‹_›)]
      exact (Reflection.checkNatDITE.WF w hnil hbool hnat htoDecTr' htoDecC htypeOK htoDecOK
        hditeOK hofTrueOK hofFalseOK hfail).mono fun _ s _ h => this (s := s) fun _ => h
    have htypeTΓ (E : c.Ext) {Γ : List VExpr} : E.venv.HasType c.lparams.length Γ w.type'
        vexpr(Prop → Bool → Prop) :=
      VEnv.HasType.weak0 E.wf (E.monoT (by rw [← hnil']; exact w.typeT))
    have hpropTrΓ {Δ : VLCtx} : TrExprS c.venv c.lparams Δ prop prop' :=
      TrExprS.of_nil_any c.Ewf (CondOK.noProj hok.prop) hpropTr
    have habTrΓ {Δ : VLCtx} : TrExprS c.venv c.lparams Δ asBool asBool' :=
      TrExprS.of_nil_any c.Ewf (CondOK.noProj hasBoolOK) habTr
    have hdecTrΓ {Δ : VLCtx} : TrExprS c.venv c.lparams Δ dec dec' :=
      TrExprS.of_nil_any c.Ewf (CondOK.noProj hok.dec) (by rw [← hnil]; exact hdecTr)
    have hclosed {v A : VExpr} (h : c.venv.HasType c.lparams.length c.vlctx.toCtx v A) :
        v.ClosedN := by
      rw [hnil'] at h; exact (h.closedN' c.Ewf.ordered.closed trivial).1
    have hdecC := hclosed hdecT
    -- the pieces' types and the gadget's equation, at a consumer's own arguments
    have H (E : c.Ext) ⦃Γ : List VExpr⦄ (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length))
        {x y : VExpr} (hx : E.venv.HasType c.lparams.length Γ x .nat)
        (hy : E.venv.HasType c.lparams.length Γ y .nat) :
        E.venv.HasType c.lparams.length Γ ((prop'.app x).app y) (.sort .zero) ∧
        E.venv.HasType c.lparams.length Γ ((asBool'.app x).app y) .bool ∧
        E.venv.HasType c.lparams.length Γ ((proof'.app x).app y)
          ((w.type'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)) ∧
        E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
          (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
            ((proof'.app x).app y)) := by
      have hed' : E.venv.IsDefEqU c.lparams.length Γ e' dec' :=
        .weak0 E.wf (E.mono (by rw [← hnil']; exact hed h4))
      have ⟨h1, h2, h3, _, h4⟩ := hgadget E hΓ hx hy
      refine ⟨h1, h2, h3, .trans E.wf hΓ ?_ ⟨_, h4⟩⟩
      simpa [VExpr.appN] using hed'.appN E.wf hΓ (vs := [x, y])  ⟨_, h4.hasType.1⟩ |>.symm
    let himpl' : ReflectNatNat.WF c asBool reflect proof := {
      asBool' := asBool', proof' := proof', hreflect := w
      hAsBool := by rw [VContext.TrExprS, hnil]; exact habTr
      hProof := by rw [VContext.TrExprS, hnil]; exact hpfTr }
    let w' : Condition.WF c ⟨prop, dec, .reflectNatNat asBool reflect proof⟩ := {
      prop' := prop', dec' := dec', himpl := himpl', hdec := hdecTr
      hprop := by show TrExprS c.venv c.lparams c.vlctx prop prop'; rw [hnil]; exact hpropTr
      vnil := hnil
      propT := by
        intro E Γ hΓ args hargs
        cases hargs with | cons hx hrest
        cases hrest with | cons hy hrest
        cases hrest
        simpa [VExpr.appN] using (H E hΓ (by simpa using hx) (by simpa using hy)).1 }
    -- `e ≡ dec`, so the consumer's decision procedure is `toDec` at the three pieces
    have hdecEq (E : c.Ext) ⦃Γ⦄ (hΓ : OnCtx Γ (E.venv.IsType c.lparams.length)) {x y}
        (hxT : E.venv.HasType c.lparams.length Γ x .nat)
        (hyT : E.venv.HasType c.lparams.length Γ y .nat) :
        E.venv.IsDefEqU c.lparams.length Γ ((dec'.app x).app y)
          (((toDec'.app ((prop'.app x).app y)).app ((asBool'.app x).app y)).app
            ((proof'.app x).app y)) := by
      have hbeta := (hgadget E hΓ hxT hyT).2.2.2
      have hed' : E.venv.IsDefEqU c.lparams.length Γ e' dec' :=
        VEnv.IsDefEqU.weak0 E.wf (E.mono (by rw [← hnil']; exact hed h4))
      obtain ⟨_, hbetaT⟩ := hbeta
      have hwfL : VExpr.WF E.venv c.lparams.length Γ ((e'.app x).app y) :=
        ⟨_, hbetaT.hasType.1⟩
      have hstep := VEnv.IsDefEqU.appN E.wf hΓ (vs := [x, y]) hed'
        (by simpa [VExpr.appN] using hwfL)
      have hbeta : E.venv.IsDefEqU c.lparams.length Γ _ _ := ⟨_, hbetaT⟩
      refine VEnv.IsDefEqU.trans E.wf hΓ ?_ hbeta
      simpa [VExpr.appN] using hstep.symm
    refine fun _ hD => ⟨w', fun hite => ?_, fun hdite => ?_⟩
    · refine ⟨Condition.WF.reflect_ite w w' rfl rfl (hI hite).2 hpropTrΓ hdecTrΓ H, ?_⟩
      -- the same equation about `VExpr`s, for a conditional reached by closing off its context
      intro E Γ args' α' t' e' be b _ hΓ hargsT happly hbe hwf
      obtain ⟨x, y, rfl, hxT, hyT⟩ : ∃ x y, args' = [x, y] ∧
          E.venv.HasType c.lparams.length Γ x .nat ∧
          E.venv.HasType c.lparams.length Γ y .nat := by
        cases hargsT with | cons h1 h2; cases h2 with | cons h3 h4
        cases h4; exact ⟨_, _, rfl, h1, h3⟩
      simp only [ConditionImpl.WF.apply] at happly
      subst happly
      refine Condition.WF.reflect_iteEval E w (hI hite).1 (hI hite).2 (htypeTΓ E)
        (H E) b hΓ hxT hyT ?_ ?_ <;> simpa [VExpr.appN]
    · refine ⟨Condition.WF.reflect_dite w w' rfl hnil hnat
        (hD hdite).1 (hD hdite).2.1 (hD hdite).2.2.1 (hD hdite).2.2.2
        hpropTrΓ hdecTrΓ htypeTΓ H, ?_, fun E Γ args' hΓ hargsT => ?_⟩
      -- the same equation as a fact about `VExpr`s, which is what a closed-off conditional needs
      · intro E Γ args' t' e' be b hΓ hargsT happly hbe hwf
        cases hargsT with | cons hxT h2; cases h2 with | cons hyT h4; cases h4
        simp only [ConditionImpl.WF.apply] at happly
        subst happly
        exact Condition.WF.reflect_diteEval E w (hD hdite).1 (hD hdite).2.1 (htypeTΓ E)
          (H E) b hΓ hxT hyT (by simpa [VExpr.appN] using hbe) (by simpa [VExpr.appN] using hwf)
      · -- and `dec` at those arguments is well typed, since `e ≡ dec` makes it `toDec`'s
        cases hargsT with | cons hxT h2; cases h2 with | cons hyT h4; cases h4
        have ⟨hpT, hblT, hHT, hdecEq⟩ := H E hΓ hxT hyT
        obtain ⟨_, h⟩ := Reflection.WF.DITE_T.toDecT (hD hdite).2.1 E hΓ hpT hblT hHT
        exact ⟨_, VEnv.HasType.defeqU_l E.wf hΓ hdecEq.symm h⟩
