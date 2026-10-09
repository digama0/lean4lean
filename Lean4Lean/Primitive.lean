import Lean4Lean.TypeChecker
import Lean4Lean.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .lam x dom body bi =>
    let d := dom.instantiateRev fvars
    withLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

namespace Primitive

deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for MVarId
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax
deriving instance ToExpr for DataValue
deriving instance ToExpr for KVMap
deriving instance ToExpr for Expr

elab (name := microQq) "q(" e:term ")" : term =>
  return toExpr (← instantiateMVars (← Elab.Term.elabTerm e none))

structure Reflection where
  type : Expr
  ofTrue : Expr
  ofFalse : Expr
  toDec : Expr

def Reflection.defn₁ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (¬true = true → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (¬false = true → ¬p) → q) → q) =>
    H fun _ h => h Bool.noConfusion)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q) =>
    if h : b = true then isTrue (H fun h' _ => h' h) else isFalse (H fun _ h' => h' h))

def Reflection.defn₂ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (true = false → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (false = false → ¬p) → q) → q) =>
    H fun _ h => h rfl)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q) =>
    b.casesOn (motive := fun b' => b = b' → Decidable p)
      (fun h => isFalse (H fun _ h' => h' h)) (fun h => isTrue (H fun h' _ => h' h)) rfl)

def Reflection.check (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.type) q(Prop → Bool → Prop) do fail

inductive ConditionImpl where
  | bool
  | reflectNatNat (asBool : Expr) (reflect : Reflection) (proof : Expr)

structure Condition where
  prop : Expr
  dec : Expr
  impl : ConditionImpl

def Condition.natLE : Condition where
  prop := q(@LE.le Nat _)
  dec := q(Nat.decLe)
  impl := .reflectNatNat
    (asBool := q(Nat.ble))
    (reflect := .defn₁)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m)))

def Condition.natEq : Condition where
  prop := q(@Eq Nat)
  dec := q(Nat.decEq)
  impl := .reflectNatNat
    (asBool := q(Nat.beq))
    (reflect := .defn₂)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)))

def Condition.bool : Condition where
  prop := q(fun x : Bool => x = true)
  dec := q(fun x => Bool.decEq x true)
  impl := .bool

def Reflection.ite (r : Reflection) : Expr :=
  .lam0 q(Prop) <| .lam0 q(Bool) <| .lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
      (mkApp3 r.toDec (.bvar 3) (.bvar 2) (.bvar 1))

def Reflection.natDITE (r : Reflection) : Expr :=
  .lam0 q(Prop) <| .lam0 q(Bool) <| .lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    mkApp2 q(@dite Nat) (.bvar 2) (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0))

def Reflection.checkITE (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.ite) (.arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) do fail
  withLocalDecl `p .default q(Prop) fun p => do
  withLocalDecl `H .default (mkApp2 r.type p q(true)) fun H => do
    unless ← isDefEq (mkApp3 r.ite p q(true) H) q(fun α : Type => fun a _ : α => a) do fail
  withLocalDecl `H .default (mkApp2 r.type p q(false)) fun H => do
    unless ← isDefEq (mkApp3 r.ite p q(false) H) q(fun α : Type => fun _ a : α => a) do fail

def Reflection.checkNatDITE (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType q(Not)) q(Prop → Prop) do fail
  unless ← isDefEq (← checkType r.natDITE) (.arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .arrow (.arrow (.bvar 2) q(Nat)) <| .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) <|
    q(Nat)) do fail
  unless ← isDefEq (← checkType r.ofTrue) (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) do fail
  unless ← isDefEq (← checkType r.ofFalse) (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) do fail
  withLocalDecl `p .default q(Prop) fun p => do
  withLocalDecl `a .default (.arrow p q(Nat)) fun a => do
  withLocalDecl `b .default (.arrow (mkApp q(Not) p) q(Nat)) fun b => do
  withLocalDecl `H .default (mkApp2 r.type p q(true)) fun H => do
    unless ← isDefEq (mkApp5 r.natDITE p q(true) H a b) (mkApp a (mkApp2 r.ofTrue p H)) do fail
  withLocalDecl `H .default (mkApp2 r.type p q(false)) fun H => do
    unless ← isDefEq (mkApp5 r.natDITE p q(false) H a b) (mkApp b (mkApp2 r.ofFalse p H)) do fail

def Condition.check (cond : Condition) (fail : ∀ {α}, M α)
    (ite := false) (dite := false) : M Unit := do
  _ ← checkType cond.dec
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    reflect.check fail
    let y := .bvar 0; let x := .bvar 1
    -- `toDec` under binders that name its argument types, applied to the three pieces. Written
    -- this way -- rather than `mkApp3 reflect.toDec …`, which it beta-reduces to -- the one
    -- `checkType` below does for all three: the arguments are checked against the binders, so
    -- `prop x y : Prop`, `asBool x y : Bool` and `proof x y : type (prop x y) (asBool x y)`,
    -- which is everything a consumer needs and consistent by construction. The four closed
    -- pieces are read only here, under the gadget's binders; those binders are inhabited (by
    -- `Nat.zero`, and then by the arguments at it), which is how the verification brings the
    -- readings out of them.
    let e := .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3
      (.lam0 q(Prop) <| .lam0 q(Bool) <| .lam0 (mkApp2 reflect.type (.bvar 1) (.bvar 0)) <|
        mkApp3 reflect.toDec (.bvar 2) (.bvar 1) (.bvar 0))
      (mkApp2 cond.prop x y) (mkApp2 asBool x y) (mkApp2 proof x y)
    _ ← checkType e
    unless ← isDefEq e cond.dec do fail
    if ite then reflect.checkITE fail
    if dite then reflect.checkNatDITE fail
  | .bool =>
    unless ← isDefEq (← checkType cond.prop) q(Bool → Prop) do fail
    let b := .bvar 0
    if ite then
      let natITE := .lam0 q(Bool) <|
        mkApp2 q(@_root_.ite Nat) (mkApp cond.prop b) (mkApp cond.dec b)
      unless ← isDefEq (← checkType natITE) q(Bool → Nat → Nat → Nat) do fail
      unless ← isDefEq (mkApp natITE q(true)) q(fun a _ : Nat => a) do fail
      unless ← isDefEq (mkApp natITE q(false)) q(fun _ a : Nat => a) do fail
    if dite then throw <| .other "unsupported"

protected def Condition.ite (cond : Condition) (α : Expr) (args : Array Expr) (t e : Expr) : Expr :=
  mkApp5 q(@ite.{1}) α (mkAppN cond.prop args) (mkAppN cond.dec args) t e

protected def Condition.dite (cond : Condition) (args: Array Expr) (t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkAppN cond.prop args) (mkAppN cond.dec args)
    (.lam0 (mkAppN cond.prop args) t)
    (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)

protected def Condition.decide (cond : Condition) (args : Array Expr) : Expr :=
  cond.ite q(Bool) args q(true) q(false)

def unfoldWellFounded (e : Expr) (fvs : Array Expr) (eq_def : Expr) (fail : ∀ {α}, M α) :
    M Expr := do
  let .app (.app _ lhs) rhs := eq_def.getForallBody.instantiateRev fvs | fail
  let orig := lhs.getAppFn
  let rhs := rhs.replace fun e' => if e' == orig then some e else none
  let .app e1 wfn ← whnf (mkAppN e fvs) | fail
  e1.withApp fun accRec args => do
  let #[α,r,_,_,n] := args | fail
  let .const ``Acc.rec [_, u] := accRec | fail
  let .app wf _ := wfn | fail
  let L := .lam0 α <| .lam0 (mkApp2 r (.bvar 0) n) (mkApp wf (.bvar 1))
  let wfn' := mkApp4 (.const ``Acc.intro [u]) α r n L
  let p ← inferType wfn
  unless ← isProp p do fail
  unless ← isDefEq p (← checkType wfn') do fail
  _ ← checkType rhs
  unless ← isDefEq (e1.app wfn') rhs do fail
  return (← getLCtx).mkLambda fvs rhs

structure Probe where
  /-- The packed argument, abstracted over the recursion variables. -/
  pack : Expr
  /-- The `ih` binder's type as a *function* `A → Sort _`: the domain of `F`'s codomain, read
  off `F`'s type once and for all. A function rather than an open term so that using it at an
  argument is an application, with no binder for a probe's context to be lifted over. -/
  dom : Expr
  /-- The fixpoint functional, asserted not to mention the recursion variables. -/
  F : Expr

def Probe.probe (P : Probe) (subst : Array Expr) (fail : ∀ {α}, M α)
    (mkRhs : Expr → Expr) : M Unit := do
  let a := (mkAppN P.pack subst)
  withLocalDecl `ih .default (mkApp P.dom a) fun ih => do
  let rhs := mkRhs ih
  _ ← checkType rhs
  unless ← isDefEq (mkApp2 P.F a ih) rhs do fail

/-- Certify that `e` is the compiled form of a well-founded recursion, and hand the equation body
to `k`.

The body is passed with recursive calls pointing at the *induction hypothesis variable* `ih`
rather than at `e`. That is what makes the caller's probes universally quantified in the
recursive-call target: consuming a unit of fuel replaces the recursive call by `Nat.fix.go` at
the lower fuel, which is not definitionally the fixpoint, so probes stated in terms of `e` would
only be usable for the outermost unfolding.

`ih` takes a proof that the measure decreases, which the caller supplies as part of the
right-hand side it returns. It is not trusted: the `checkType` in `probe` rejects the definition
if it does not have the type `ih` demands.

Returns the probe function and the packing function `fun fvs => a₀`, which the caller needs to
name the arguments of a recursive call.

`meas` is a closed lambda -- `fun m _ : Nat => m` for `Nat.gcd` -- rather than an expression in
the caller's context: its telescope supplies the arity and the argument types, so the recognizer
opens its own scope for the destructuring and nothing found there escapes except the closed
`pack`/`dom` abstractions and `F`, which is checked closed. Probes then run in whatever context
the *caller* is in when it calls them, so different probes can bind different variables -- they
correspond to the variables of a pattern, not to the arguments of the function. -/
def unfoldNatWellFounded (e meas : Expr) (fail : ∀ {α}, M α) : M Probe := do
  let succ := mkApp q(Nat.succ)
  let (F, pack) ← lambdaTelescope meas fun fvs meas => do
    _ ← checkType (mkAppN e fvs)
    let e1 ← whnfCore (mkAppN e fvs) -- get _unary
    let e1 ← unfoldDefinition e1 -- get fix
    (← whnfCore e1).withApp fun fix args => do
    let .const ``WellFounded.Nat.fix [_, _] := fix | fail
    let #[α,motive,f,F,a₀] := args | fail
    let fixFn := mkAppN fix #[α,motive,f,F]
    let ty ← inferType a₀
    withLocalDecl `a .default ty fun a => do
      unless ← isDefEq (← checkType (.app f a)) q(Nat) do fail
      -- prove |- f a₀ ≡ meas
      unless ← isDefEq (.app f a₀) meas do fail
      -- prove |- fix α motive f F a ≡ go α motive f F (eager (succ (f a))) a [proof]
      let e1 ← unfoldDefinition (.app fixFn a) -- get fix.go
      let e1 ← whnfCore e1
      e1.withApp fun fixGo args => do
      let #[α',motive',f',F',fuel,a',pf] := args | fail
      unless (α, motive, f, F, a) == (α', motive', f', F', a') do fail
      let .app eager n := fuel | fail
      unless ← isProp (← inferType pf) do fail
      unless ← isDefEq n (succ (.app f a)) do fail
      -- prove |- eager n = if beq n n = true then n else n
      unless (← getEnv).contains ``Nat.beq do fail
      withLocalDecl `x .default q(Nat) fun x => do
        unless ← isDefEq (mkApp eager x)
          (Condition.bool.ite q(Nat) #[mkApp2 (.const ``Nat.beq []) x x] x x) do fail
      -- prove |- go α motive f F (succ t) x hfuel ≡ F x fun y hy => go α motive f F t y [proof]
      let go' ← unfoldDefinition fixGo -- get fix
      lambdaTelescope go' fun fvs go' => do
      let #[_,_,_,F,t] := fvs | fail
      let .app natRec t' := go' | fail
      unless !natRec.containsFVar t.fvarId! && t == t' do fail
      _ ← checkType (succ t)
      let gor ← whnfCore (.app natRec (succ t))
      lambdaTelescope gor fun fvs gor => do
      let #[x,_] := fvs | fail
      let .app Fx ih := gor | fail
      unless .app F x == Fx do fail
      lambdaTelescope ih fun fvs ih => do
      let #[y,_] := fvs | fail
      let .app ih _ := ih | fail
      unless ih == .app (.app natRec t) y do fail
    -- ensure `F` does not depend on the `fvs`
    let lctx ← getLCtx
    let F := F.abstract fvs
    if F.hasLooseBVars then fail
    -- `F : (a : ty) → Dom a → motive a`: the packed argument's type is `F`'s domain.
    let .forallE _ A _ _ ← whnf (← inferType F) | fail
    unless ← isDefEq ty A do fail
    return (F, lctx.mkLambda fvs a₀)
  -- `F`'s type is read again here, in the context the probe is returned to, and the `ih` binder's
  -- type `Dom` is computed from that reading: what was found about `F` under the measure's
  -- binders is not carried out of them. (`F` itself is well typed here: it mentions none of those
  -- binders, which are `Nat`s, so substituting `Nat.zero` for them leaves it alone.)
  let .forallE _ A cod _ ← whnf (← inferType F) | fail
  let dom ← withLocalDecl `a .default A fun a => do
    let .forallE _ dom _ _ ← whnf (cod.instantiate1 a) | fail
    return .lam `a A (dom.abstract #[a]) .default
  return { F, dom, pack }

/-! ### The recognizer's vocabulary

`checkDef` writes its equations with these; they were `let`s in its body until the clauses became
definitions of their own and needed them too. The `Expr`s are constants so that they are built
once; the functions are `@[inline]` so that a use still compiles to the application it was. -/

/-- The definition is a safe one with no universe parameters. -/
@[inline] def ok (v : DefinitionVal) : Bool := v.safety == .safe && v.levelParams.isEmpty

/-- What every check throws on failure. -/
@[inline] def fail (v : DefinitionVal) {α} : M α :=
  throw <| .other s!"invalid form for primitive def {v.name}"

def tru : Expr := q(true)
def fal : Expr := q(false)
def zero : Expr := q(Nat.zero)
@[inline] def succ : Expr → Expr := mkApp q(Nat.succ)
@[inline] def pred : Expr → Expr := mkApp q(Nat.pred)
@[inline] def add : Expr → Expr → Expr := mkApp2 q(Nat.add)
@[inline] def sub : Expr → Expr → Expr := mkApp2 q(Nat.sub)
@[inline] def mul : Expr → Expr → Expr := mkApp2 q(Nat.mul)
@[inline] def mod : Expr → Expr → Expr := mkApp2 q(Nat.mod)
@[inline] def div : Expr → Expr → Expr := mkApp2 q(Nat.div)
def one : Expr := succ zero
def two : Expr := succ one

@[inline] def checkNatAdd (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat && ok v do fail v
  -- add : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let add := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  -- add x 0 ≡ x
  unless ← isDefEq (add x zero) x do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  -- add y (succ x) ≡ succ (add y x)
  unless ← isDefEq (add x (succ y)) (succ (add x y)) do fail v

@[inline] def checkNatPred (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat && ok v do fail v
  -- pred : Nat → Nat
  unless v.type == q(@& Nat → Nat) do fail v
  let pred := mkApp v.value
  unless ← isDefEq (pred zero) zero do fail v
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (pred (succ x)) x do fail v

@[inline] def checkNatSub (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.pred && ok v do fail v
  -- sub : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let sub := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (sub x zero) x do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (sub x (succ y)) (pred (sub x y)) do fail v

@[inline] def checkNatMul (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.add && ok v do fail v
  -- mul : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let mul := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (mul x zero) zero do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (mul x (succ y)) (add (mul x y) x) do fail v

@[inline] def checkNatPow (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.mul && ok v do fail v
  -- pow : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let pow := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (pow x zero) one do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (pow x (succ y)) (mul (pow x y) x) do fail v

open private Nat.gcd._unary._proof_1 in Nat.gcd._unary in
@[inline] def checkNatGcd (v : DefinitionVal) : M Unit := do
  let env ← getEnv
  unless env.contains ``Nat.mod && env.contains ``Bool && ok v do fail v
  -- gcd : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  Condition.bool.check (fail v) (ite := true)
  let P ← unfoldNatWellFounded v.value q(fun m _n : Nat => m) (fail v)
  -- the base pattern `(0, n)` binds one variable, the step pattern `(m+1, n)` binds two
  withLocalDecl `n .default q(Nat) fun n => do
  P.probe #[zero, n] (fail v) fun _ => n
  withLocalDecl `m .default q(Nat) fun m => do
  P.probe #[succ m, n] (fail v) fun ih =>
    mkApp2 ih (mkApp2 P.pack (mod n (succ m)) (succ m))
      (mkApp2 q(fun m n : Nat =>
        Nat.gcd._unary._proof_1 m.succ n (Nat.ne_of_beq_eq_false (Eq.refl false))) m n)

/-- The four constructor cases of a `Nat → Nat → Bool` recurrence: `true` on `0 0`, the
diagonal `f (succ x) (succ y) ≡ f x y`, `false` on `(succ x) 0`, and `b0s` on `0 (succ x)`,
which is all that separates `Nat.beq` from `Nat.ble`. -/
@[inline] def checkNatBoolCases (v : DefinitionVal) (b0s : Expr) : M Unit := do
  let env ← getEnv
  unless env.contains ``Nat && env.contains ``Bool && ok v do fail v
  -- f : Nat → Nat → Bool
  unless v.type == q(@& Nat → @& Nat → Bool) do fail v
  let f := mkApp2 v.value
  unless ← isDefEq (f zero zero) tru do fail v
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (f zero (succ x)) b0s do fail v
  unless ← isDefEq (f (succ x) zero) fal do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (f (succ x) (succ y)) (f x y) do fail v

@[inline] def checkNatBEq (v : DefinitionVal) : M Unit := checkNatBoolCases v fal

@[inline] def checkNatBLE (v : DefinitionVal) : M Unit := checkNatBoolCases v tru

open private Nat.bitwise._unary._proof_1 in Nat.bitwise._unary in
@[inline] def checkNatBitwise (v : DefinitionVal) : M Unit := do
  let env ← getEnv
  unless env.contains ``Nat && env.contains ``Bool && ok v do fail v
  -- bitwise : Nat → Nat → Nat
  unless v.type == q((Bool → Bool → Bool) → Nat → Nat → Nat) do fail v
  let c := Condition.natEq; c.check (fail v) (ite := true) (dite := true)
  let bc := Condition.bool; bc.check (fail v) (ite := true)
  withLocalDecl `f .default q(Bool → Bool → Bool) fun f => do
  let P ← unfoldNatWellFounded (v.value.app f) q(fun m _n : Nat => m) (fail v)
  withLocalDecl `n .default q(Nat) fun n => do
  withLocalDecl `m .default q(Nat) fun m => do
  P.probe #[n, m] (fail v) fun ih =>
    c.dite #[n, zero] (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
    c.ite q(Nat) #[m, zero] (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
    let n' := div n two
    let m' := div m two
    let b₁ := c.decide #[mod n two, one]
    let b₂ := c.decide #[mod m two, one]
    let r := mkApp2 ih (mkApp2 P.pack n' m')
      (mkApp3 q(Nat.bitwise._unary._proof_1) n m (.bvar 0))
    bc.ite q(Nat) #[mkApp2 f b₁ b₂] (add (add r r) one) (add r r)

@[inline] def checkNatLAnd (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.bitwise && ok v do fail v
  -- land : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let .app (.const ``Nat.bitwise []) and := v.value | fail v
  let and := mkApp2 and
  withLocalDecl `x .default q(Bool) fun x => do
  unless ← isDefEq (and fal x) fal do fail v
  unless ← isDefEq (and tru x) x do fail v

@[inline] def checkNatLOr (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.bitwise && ok v do fail v
  -- lor : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let .app (.const ``Nat.bitwise []) or := v.value | fail v
  let or := mkApp2 or
  withLocalDecl `x .default q(Bool) fun x => do
  unless ← isDefEq (or fal x) x do fail v
  unless ← isDefEq (or tru x) tru do fail v

@[inline] def checkNatXor (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.bitwise && ok v do fail v
  -- xor : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let .app (.const ``Nat.bitwise []) xor := v.value | fail v
  let xor := mkApp2 xor
  unless ← isDefEq (xor fal fal) fal do fail v
  unless ← isDefEq (xor tru fal) tru do fail v
  unless ← isDefEq (xor fal tru) tru do fail v
  unless ← isDefEq (xor tru tru) fal do fail v

@[inline] def checkNatShiftLeft (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.mul && ok v do fail v
  -- shiftLeft : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let shl := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (shl x zero) x do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (shl x (succ y)) (shl (mul two x) y) do fail v

@[inline] def checkNatShiftRight (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat.div && ok v do fail v
  -- shiftRight : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  let shr := mkApp2 v.value
  withLocalDecl `x .default q(Nat) fun x => do
  unless ← isDefEq (shr x zero) x do fail v
  withLocalDecl `y .default q(Nat) fun y => do
  unless ← isDefEq (shr x (succ y)) (div (shr x y) two) do fail v

@[inline] def checkCharOfNat (v : DefinitionVal) : M Unit := do
  unless (← getEnv).contains ``Nat && ok v do fail v
  -- Char : Type
  _ ← ensureType q(Char) (inferOnly := false)
  -- @Char.ofNat : Nat → Char
  unless v.type == q(Nat → Char) do fail v

@[inline] def checkStringOfList (v : DefinitionVal) : M Unit := do
  unless ok v do fail v
  -- List Char : Type
  _ ← ensureType q(List Char) (inferOnly := false)
  -- Char : Type
  _ ← ensureType q(Char)
  -- @List.nil.{0} Char : List Char
  unless ← isDefEq (← checkType q(List.nil (α := Char))) q(List Char) do fail v
  -- @List.cons.{0} Char : Char → List Char → List Char
  unless ← isDefEq (← checkType q(List.cons (α := Char))) q(Char → List Char → List Char) do fail v
  -- String.ofList : List Char → String
  unless v.type == q(List Char → String) do fail v

/-- The fuel recursion `Nat.mod` and `Nat.div` share: the `≤` they are stated with, the
`go` they recurse through, the condition their conditionals test, and then two equations at
the recursion's own variables -- the caller's top equation, and `go`'s own.

The two clauses differ in four places, which are the parameters: which `go` it is, what the top
equation's left hand side applies the definition to (`succ x` for `Nat.mod`, `x` for `Nat.div`),
what that equation's right hand side is, and what `go`'s equation does with the recursive call
(`Nat.div` counts the steps, `Nat.mod` does not) and returns when the recursion stops.

`ite` is on when the top equation needs the conditional's non-dependent form, which only
`Nat.mod` does. -/
@[inline] def checkNatFuelRec (v : DefinitionVal) (goName : Name) (ite := false)
    (lhs : Expr → Expr) (H : Expr → Expr) (els : Expr → Expr)
    (top : (Expr → Expr → Expr → Expr → Expr → Expr) → Expr → Expr → Expr) : M Unit := do
  unless ← isDefEq (← checkType q(@LE.le Nat _)) q(Nat → Nat → Prop) do fail v
  let le := mkApp2 q(@LE.le Nat _)
  unless ← isDefEq (← checkType (.const goName []))
    q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail v
  let go := mkApp5 (.const goName [])
  let c := Condition.natLE; c.check (fail v) (ite := ite) (dite := true)
  withLocalDecl `x .default q(Nat) fun x => do
  withLocalDecl `y .default q(Nat) fun y => do
  let e := top go x y
  _ ← checkType e
  unless ← isDefEq (mkApp2 v.value (lhs x) y) e do fail v
  withLocalDecl `hy .default (le one y) fun hy => do
  withLocalDecl `fuel .default q(Nat) fun fuel => do
  withLocalDecl `h .default (le (succ x) (succ fuel)) fun h => do
  let e := c.dite #[y, x] (H (go y hy fuel (sub x y)
    (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) (els x)
  _ ← checkType e
  unless ← isDefEq (go y hy (succ fuel) x h) e do fail v

/-- `Nat.mod`'s clause of the recognizer: the base equation `mod 0 x ≡ 0`, then the shared fuel
recursion through `Nat.modCore.go`, whose top equation is
`mod (succ x) y ≡ if y ≤ succ x then (if 1 ≤ y then go … else succ x) else succ x`.

The clause is a definition rather than a `match` arm so that its verification can be a theorem of
its own; `@[inline]` puts it back where it was for the compiler. -/
@[inline] def checkNatMod (v : DefinitionVal) : M Unit := do
  let env ← getEnv
  unless env.contains ``Nat.sub && env.contains ``Bool && ok v do fail v
  -- mod : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  withLocalDecl `x .default q(Nat) fun x => do
    unless ← isDefEq (mkApp2 v.value zero x) zero do fail v
  checkNatFuelRec v ``Nat.modCore.go (ite := true) (lhs := succ) (H := id) (els := id) fun go x y =>
    let c := Condition.natLE; let sx := succ x
    c.ite q(Nat) #[y, sx] (c.dite #[one, y]
      (go y (.bvar 0) (succ sx) sx (mkApp q(Nat.lt_succ_self) sx)) sx) sx

/-- `Nat.div`'s clause: the same recursion through `Nat.div.go`, with no base equation -- `div 0 y`
is covered by the top equation `div x y ≡ if 1 ≤ y then go y _ (succ x) x _ else 0` -- and a
`succ` around the recursive call. -/
@[inline] def checkNatDiv (v : DefinitionVal) : M Unit := do
  let env ← getEnv
  unless env.contains ``Nat.sub && env.contains ``Bool && ok v do fail v
  -- div : Nat → Nat → Nat
  unless v.type == q(@& Nat → @& Nat → Nat) do fail v
  checkNatFuelRec v ``Nat.div.go (lhs := id) (H := succ) (els := fun _ => zero)
    (top := fun go x y =>
      Condition.natLE.dite #[one, y]
        (go y (.bvar 0) (succ x) x (mkApp q(Nat.lt_succ_self) x)) zero)

def checkDef (v : DefinitionVal) : M Bool := do
  match v.name with
  | ``Nat.add => checkNatAdd v
  | ``Nat.pred => checkNatPred v
  | ``Nat.sub => checkNatSub v
  | ``Nat.mul => checkNatMul v
  | ``Nat.pow => checkNatPow v
  | ``Nat.mod => checkNatMod v
  | ``Nat.div => checkNatDiv v
  | ``Nat.gcd => checkNatGcd v
  | ``Nat.beq => checkNatBEq v
  | ``Nat.ble => checkNatBLE v
  | ``Nat.bitwise => checkNatBitwise v
  | ``Nat.land => checkNatLAnd v
  | ``Nat.lor => checkNatLOr v
  | ``Nat.xor => checkNatXor v
  | ``Nat.shiftLeft => checkNatShiftLeft v
  | ``Nat.shiftRight => checkNatShiftRight v
  | ``Char.ofNat => checkCharOfNat v
  | ``String.ofList => checkStringOfList v
  | _ => return false
  return true

def checkInductive (_env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Except Exception Bool := do
  unless !isUnsafe && lparams.isEmpty && nparams == 0 do return false
  let [type] := types | return false
  unless type.type == .sort (.succ .zero) do return false
  let fail {α} : Except Exception α :=
    throw <| .other s!"invalid form for primitive inductive {type.name}"
  match type.name with
  | ``Bool =>
    let [⟨``false, .const ``Bool []⟩, ⟨``true, .const ``Bool []⟩] := type.ctors | fail
  | ``Nat =>
    let [
      ⟨``Nat.zero, .const ``Nat []⟩,
      ⟨``Nat.succ, .forallE _ (.const ``Nat []) (.const ``Nat []) _⟩
    ] := type.ctors | fail
  | _ => return false
  return true

-- Self-test to ensure that the primitives check at compile time
run_meta
  let env ← Lean.getEnv
  for c in Environment.primitives do
    match env.find? c with
    | some (.defnInfo v) =>
      let (.true, _) ← Elab.Term.TermElabM.run (checkDef v)
        | throwError "{v.name}"
    | some (.inductInfo _) | some (.ctorInfo _) => pure ()
    | r => throwError "unexpected primitive: {r.map (·.name)}"
