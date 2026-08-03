import Lean4Lean.TypeChecker
import Lean4Lean.Environment.Basic

namespace Lean4Lean
namespace Environment
open Lean hiding Environment Exception
open Kernel TypeChecker

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

def Condition.boolNatITE (cond : Condition) : Expr :=
  .lam0 q(Bool) <| mkApp2 q(@_root_.ite Nat)
    (mkApp cond.prop (.bvar 0))
    (mkApp cond.dec (.bvar 0))

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
  let trueLhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
    mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let trueRhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
    .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  unless ← isDefEq trueLhs trueRhs do fail
  let falseLhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
    mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let falseRhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
    .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  unless ← isDefEq falseLhs falseRhs do fail

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
  let close (truth : Expr) (body : Expr) :=
    .lam0 q(Prop) <|
    .lam0 (.arrow (.bvar 0) q(Nat)) <|
    .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
    .lam0 (mkApp2 r.type (.bvar 2) truth) body
  let trueLhs := close q(true) <|
    mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)
  let trueRhs := close q(true) <|
    mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))
  unless ← isDefEq trueLhs trueRhs do fail
  let falseLhs := close q(false) <|
    mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)
  let falseRhs := close q(false) <|
    mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))
  unless ← isDefEq falseLhs falseRhs do fail

def Condition.check (cond : Condition) (fail : ∀ {α}, M α)
    (ite := false) (dite := false) : M Unit := do
  _ ← checkType cond.dec
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    unless ← isDefEq (← inferType cond.prop) q(Nat → Nat → Prop) do fail
    reflect.check fail
    if ite then reflect.checkITE fail
    if dite then reflect.checkNatDITE fail
    let y := .bvar 0; let x := .bvar 1
    let e := .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
      (mkApp2 cond.prop x y) (mkApp2 asBool x y) (mkApp2 proof x y)
    _ ← checkType e
    let decideFn := .lam0 q(Nat) <| .lam0 q(Nat) <|
      mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)
    unless ← isDefEq (← inferType decideFn) q(Nat → Nat → Bool) do fail
    unless ← isDefEq (← inferType asBool) q(Nat → Nat → Bool) do fail
    unless ← isProp (← inferType proof) do fail
    unless ← isDefEq e cond.dec do fail
  | .bool =>
    unless ← isDefEq (← inferType cond.prop) q(Bool → Prop) do fail
    if ite then
      let natITE := cond.boolNatITE
      unless ← isDefEq (← checkType natITE) q(Bool → Nat → Nat → Nat) do fail
      unless ← isDefEq (mkApp natITE q(true))
        (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) do fail
      unless ← isDefEq (mkApp natITE q(false))
        (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) do fail
    if dite then throw <| .other "unsupported"

protected def Condition.ite (cond : Condition) (α : Expr) (args : Array Expr) (t e : Expr) : Expr :=
  mkApp5 q(@ite.{1}) α (mkAppN cond.prop args) (mkAppN cond.dec args) t e

protected def Condition.dite (cond : Condition) (args: Array Expr) (t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkAppN cond.prop args) (mkAppN cond.dec args)
    (.lam0 (mkAppN cond.prop args) t)
    (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)

/-- Use the selector whose equations were checked by `Condition.check`.
For reflected Nat conditions this avoids throwing away the Boolean reflection
witness and reconstructing the same selector through a raw `ite`. -/
protected def Condition.reflectedITE (cond : Condition) (α : Expr)
    (args : Array Expr) (t e : Expr) : Expr :=
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    mkApp6 reflect.ite (mkAppN cond.prop args) (mkAppN asBool args)
      (mkAppN proof args) α t e
  | .bool => cond.ite α args t e

/-- Dependent counterpart of `Condition.reflectedITE`. -/
protected def Condition.reflectedDITE (cond : Condition) (args : Array Expr)
    (t e : Expr) : Expr :=
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    mkApp5 reflect.natDITE (mkAppN cond.prop args) (mkAppN asBool args)
      (mkAppN proof args)
      (.lam0 (mkAppN cond.prop args) t)
      (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)
  | .bool => cond.dite args t e

protected def Condition.decide (cond : Condition) (args : Array Expr) : Expr :=
  cond.ite q(Bool) args q(true) q(false)

def unfoldWellFounded (e : Expr) (fvs : Array Expr) (eq_def : Expr) (fail : ∀ {α}, M α) : M Expr := do
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

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .lam x dom body bi =>
    let d := dom.instantiateRev fvars
    withLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

def forallTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .forallE x dom body bi =>
    let d := dom.instantiateRev fvars
    withLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

def withLambda (e : Expr) (fail : ∀ {α}, M α) (k : Expr → Expr → M α) : M α :=
  match e with
  | .lam name dom body bi =>
    withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)
  | _ => fail

def withForall (e : Expr) (fail : ∀ {α}, M α) (k : Expr → Expr → M α) : M α :=
  match e with
  | .forallE name dom body bi =>
    withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)
  | _ => fail

/-- A transparent version of expression alpha-equivalence for certificate
shape checks.  Unlike Lean's opaque `Expr.eqv`, this relation can be connected
to the verified expression translation. -/
def exprShapeEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' => exprShapeEq f f' && exprShapeEq a a'
  | .lam _ ty body _, .lam _ ty' body' _ =>
    exprShapeEq ty ty' && exprShapeEq body body'
  | .forallE _ ty body _, .forallE _ ty' body' _ =>
    exprShapeEq ty ty' && exprShapeEq body body'
  | .letE _ ty val body _, .letE _ ty' val' body' _ =>
    exprShapeEq ty ty' && exprShapeEq val val' && exprShapeEq body body'
  | .lit l, .lit l' => l == l'
  | .mdata _ e, .mdata _ e' => exprShapeEq e e'
  | .proj s i e, .proj s' i' e' =>
    s == s' && i == i' && exprShapeEq e e'
  | _, _ => false

/-- The implementation pieces recovered while validating a compiled
`WellFounded.Nat.fix`.  They remain in the caller's local context; consumers
can instantiate `fixFn`/`fixGo` at concrete states and close the resulting
certificate before leaving that context. -/
structure NatWellFoundedCoreResult where
  equation : Expr
  fixFn : Expr
  fixGo : Expr
  goFn : Expr
  measure : Expr
  functional : Expr
  state : Expr
  callLhs : Expr
  callRhs : Expr
  entryLhs : Expr
  entryRhs : Expr
  topLhs : Expr
  topRhs : Expr
  eagerFn : Expr
  eagerLhs : Expr
  eagerRhs : Expr
  boolTrueLhs : Expr
  boolTrueRhs : Expr
  boolFalseLhs : Expr
  boolFalseRhs : Expr
  stepLhs : Expr
  stepRhs : Expr
  specStepLhs : Expr
  specStepRhs : Expr

def unfoldNatWellFoundedCore (e : Expr) (fvs : Array Expr) (eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let succ := mkApp q(Nat.succ)
  let x : Expr := .bvar 0
  let .app (.app _ lhs) rhs := eq_def.getForallBody.instantiateRev fvs | fail
  let orig := lhs.getAppFn
  let rhs := rhs.replace fun e' => if e' == orig then some e else none
  let e1 ← whnfCore (mkAppN e fvs) -- get _unary
  let e1 ← unfoldDefinition e1 -- get fix
  (← whnfCore e1).withApp fun fix args => do
  let .const ``WellFounded.Nat.fix [_, _] := fix | fail
  let #[α,motive,f,F,a₀] := args | fail
  let fixFn := mkAppN fix #[α,motive,f,F]
  let call ← unfoldDefinition (.app fixFn a₀)
  let call ← whnfCore call
  let fixGo₀ ← call.withApp fun fixGo args => do
    let #[α',motive',f',F',fuel,a',_] := args | fail
    unless (α, motive, f, F, a₀) == (α', motive', f', F', a') do fail
    let .app _ _ := fuel | fail
    return fixGo
  let callLhs := (← getLCtx).mkLambda fvs (mkAppN e fvs)
  let callRhs := (← getLCtx).mkLambda fvs call
  unless ← isDefEq callLhs callRhs do fail
  let goFn := (← getLCtx).mkLambda fvs (mkAppN fixGo₀ #[α, motive, f, F])
  let entryLhs := (← getLCtx).mkLambda fvs (mkAppN e fvs)
  let entryRhs := (← getLCtx).mkLambda fvs (mkAppN fix args)
  unless ← isDefEq entryLhs entryRhs do fail
  withLocalDecl `a .default (← inferType a₀) fun a => do
  -- prove |- fix α motive f F a ≡ go α motive f F (eager (f a)) a [proof]
  let e1 ← unfoldDefinition (.app fixFn a) -- get fix.go
  let e1 ← whnfCore e1
  let topLhs := (← getLCtx).mkLambda (fvs.push a) (.app fixFn a)
  let topRhs := (← getLCtx).mkLambda (fvs.push a) e1
  unless ← isDefEq topLhs topRhs do fail
  let (fixGo, eagerFn, eagerLhs, eagerRhs, boolTrueLhs, boolTrueRhs,
      boolFalseLhs, boolFalseRhs, stepLhs, stepRhs) ←
    e1.withApp fun fixGo args => do
    let #[α',motive',f',F',fuel,a',_] := args | fail
    unless (α, motive, f, F, a) == (α', motive', f', F', a') do fail
    unless fixGo == fixGo₀ do fail
    let .app eager n := fuel | fail
    unless ← isDefEq n (succ (.app f a)) do fail
    -- prove |- eager n = if beq n n = true then n else n
    unless (← getEnv).contains ``Nat.beq do fail
    let c := Condition.bool; c.check (fail) (ite := true)
    let boolTrueLhs := mkApp c.boolNatITE q(true)
    let boolTrueRhs := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1
    let boolFalseLhs := mkApp c.boolNatITE q(false)
    let boolFalseRhs := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0
    unless ← isDefEq boolTrueLhs boolTrueRhs do fail
    unless ← isDefEq boolFalseLhs boolFalseRhs do fail
    let eagerLhs := .lam0 q(Nat) (mkApp eager x)
    let eagerRhs := .lam0 q(Nat)
      (mkApp3 c.boolNatITE (mkApp2 (.const ``Nat.beq []) x x) x x)
    unless ← isDefEq eagerLhs eagerRhs do fail
    -- prove |- go α motive f F (succ t) x hfuel ≡ F x fun y hy => go α motive f F t y [proof]
    let go' ← unfoldDefinition fixGo -- get fix
    withLambda go' fail fun αv go' =>
    withLambda go' fail fun motivev go' =>
    withLambda go' fail fun fv go' =>
    withLambda go' fail fun F go' =>
    withLambda go' fail fun t go' => do
    let .app natRec t' := go' | fail
    unless !natRec.containsFVar t.fvarId! && t == t' do fail
    _ ← checkType (succ t)
    let gor ← whnfCore (.app natRec (succ t))
    let stepLhs := (← getLCtx).mkLambda #[αv, motivev, fv, F, t]
      (mkAppN fixGo #[αv, motivev, fv, F, succ t])
    let goPred := mkAppN fixGo #[αv, motivev, fv, F, t]
    let gor' := gor.replace fun e' =>
      if e' == .app natRec t then some goPred else none
    let stepRhs := (← getLCtx).mkLambda #[αv, motivev, fv, F, t] gor'
    unless ← isDefEq stepLhs stepRhs do fail
    withLambda gor fail fun x gor =>
    withLambda gor fail fun _ gor => do
    let .app Fx ih := gor | fail
    unless .app F x == Fx do fail
    withLambda ih fail fun y ih =>
    withLambda ih fail fun _ ih => do
    let .app ih _ := ih | fail
    unless ih == .app (.app natRec t) y do fail
    return (fixGo, eager, eagerLhs, eagerRhs, boolTrueLhs, boolTrueRhs,
      boolFalseLhs, boolFalseRhs, stepLhs, stepRhs)
  let specStepLhs ← whnfCore (mkAppN stepLhs #[α, motive, f, F])
  let specStepRhs ← whnfCore (mkAppN stepRhs #[α, motive, f, F])
  let specStepLhs := (← getLCtx).mkLambda fvs specStepLhs
  let specStepRhs := (← getLCtx).mkLambda fvs specStepRhs
  unless ← isDefEq specStepLhs specStepRhs do fail
  -- prove |- rhs ≡ F x fun y _ => fix α motive f F y
  let .forallE _ dom _ _ ← inferType (.app F a₀) | fail
  let ih' ← withForall dom fail fun y dom =>
    withForall dom fail fun h _ => do
    return (← getLCtx).mkLambda #[y, h] (.app fixFn y)
  have rhs' := mkApp2 F a₀ ih'
  _ ← checkType rhs'
  unless ← isDefEq rhs rhs' do fail
  return {
    equation := (← getLCtx).mkLambda fvs rhs
    fixFn
    fixGo
    goFn
    measure := f
    functional := F
    state := a₀
    callLhs
    callRhs
    entryLhs
    entryRhs
    topLhs
    topRhs
    eagerFn
    eagerLhs
    eagerRhs
    boolTrueLhs
    boolTrueRhs
    boolFalseLhs
    boolFalseRhs
    stepLhs
    stepRhs
    specStepLhs
    specStepRhs
  }

@[irreducible] def checkNatWellFoundedEquation
    (lhs rhs : Expr) : M Unit := do
  let fail {α} : M α := throw <| .other "invalid well-founded recursion certificate"
  unless !lhs.hasFVar && !lhs.hasMVar && !rhs.hasFVar && !rhs.hasMVar do fail
  _ ← checkType lhs
  _ ← checkType rhs
  unless ← isDefEq lhs rhs do fail

def NatWellFoundedCoreResult.expectedEagerLhs
    (r : NatWellFoundedCoreResult) : Expr :=
  let x : Expr := .bvar 0
  .lam0 q(Nat) <| mkApp r.eagerFn x

def NatWellFoundedCoreResult.expectedEagerRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  let x : Expr := .bvar 0
  .lam0 q(Nat) <| mkApp3 Condition.bool.boolNatITE
    (mkApp2 (.const ``Nat.beq []) x x) x x

def NatWellFoundedCoreResult.expectedBoolTrueLhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  mkApp Condition.bool.boolNatITE q(true)

def NatWellFoundedCoreResult.expectedBoolTrueRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1

def NatWellFoundedCoreResult.expectedBoolFalseLhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  mkApp Condition.bool.boolNatITE q(false)

def NatWellFoundedCoreResult.expectedBoolFalseRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0

def NatWellFoundedCoreResult.auxShape (r : NatWellFoundedCoreResult) : Bool :=
  exprShapeEq r.eagerLhs r.expectedEagerLhs &&
  exprShapeEq r.eagerRhs r.expectedEagerRhs &&
  exprShapeEq r.boolTrueLhs r.expectedBoolTrueLhs &&
  exprShapeEq r.boolTrueRhs r.expectedBoolTrueRhs &&
  exprShapeEq r.boolFalseLhs r.expectedBoolFalseLhs &&
  exprShapeEq r.boolFalseRhs r.expectedBoolFalseRhs &&
  exprShapeEq r.eagerFn q(WellFounded.Nat.eager) &&
  !r.goFn.hasLooseBVars

@[irreducible] def checkNatWellFoundedCertificate
    (r : NatWellFoundedCoreResult) : M Unit := do
  unless r.auxShape do
    throw <| .other "invalid well-founded recursion auxiliary certificate"
  checkNatWellFoundedEquation r.callLhs r.callRhs
  checkNatWellFoundedEquation r.entryLhs r.entryRhs
  checkNatWellFoundedEquation r.topLhs r.topRhs
  checkNatWellFoundedEquation r.eagerLhs r.eagerRhs
  checkNatWellFoundedEquation r.boolTrueLhs r.boolTrueRhs
  checkNatWellFoundedEquation r.boolFalseLhs r.boolFalseRhs
  checkNatWellFoundedEquation r.stepLhs r.stepRhs
  checkNatWellFoundedEquation r.specStepLhs r.specStepRhs

/-- Turn the equation theorem's outer telescope into a lambda and replace its
original function head by the candidate primitive implementation. -/
def natWellFoundedEquation (e : Expr) : Expr → Option Expr
  | .forallE name dom body bi =>
    (natWellFoundedEquation e body).map fun body => .lam name dom body bi
  | .app (.app _ lhs) rhs =>
    some <| rhs.replace fun e' => if e' == lhs.getAppFn then some e else none
  | _ => none

/-- The closed branch equation checked for a candidate implementation of
`Nat.bitwise`. -/
def natBitwiseEquation (bitwise : Expr) : Expr :=
  let f := .bvar 2
  let n := .bvar 1
  let m := .bvar 0
  let zero := q(Nat.zero)
  let one := mkApp q(Nat.succ) zero
  let two := mkApp q(Nat.succ) one
  let add := mkApp2 q(Nat.add)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let bitwise := mkApp3 bitwise
  let c := Condition.natEq
  let bc := Condition.bool
  let body :=
    c.ite q(Nat) #[n, zero] (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
    c.ite q(Nat) #[m, zero] (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
    let n' := div n two
    let m' := div m two
    let b₁ := c.decide #[mod n two, one]
    let b₂ := c.decide #[mod m two, one]
    let r := bitwise f n' m'
    bc.ite q(Nat) #[mkApp2 f b₁ b₂] (add (add r r) one) (add r r)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) body

def natBitwiseZeroEquation (equation : Expr) : Expr × Expr :=
  let f := .bvar 1
  let b := .bvar 0
  let zero := q(Nat.zero)
  let close body := .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f zero b,
    close <| mkApp3 Condition.bool.boolNatITE (mkApp2 f q(false) q(true)) b zero)

def natBitwiseZeroRightEquation (equation : Expr) : Expr × Expr :=
  let f := .bvar 1
  let zero := q(Nat.zero)
  let a := mkApp q(Nat.succ) (.bvar 0)
  let close body := .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f a zero,
    close <| mkApp3 Condition.bool.boolNatITE (mkApp2 f q(true) q(false)) a zero)

def natBitwiseSuccEquation (equation bitwise : Expr) : Expr × Expr :=
  let f := .bvar 2
  let a := mkApp q(Nat.succ) (.bvar 1)
  let b := mkApp q(Nat.succ) (.bvar 0)
  let zero := q(Nat.zero)
  let one := mkApp q(Nat.succ) zero
  let two := mkApp q(Nat.succ) one
  let add := mkApp2 q(Nat.add)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let c := Condition.natEq
  let n' := div a two
  let m' := div b two
  let b₁ := c.decide #[mod a two, one]
  let b₂ := c.decide #[mod b two, one]
  let r := mkApp3 bitwise f n' m'
  let close body := .lam0 q(Bool → Bool → Bool) <|
    .lam0 q(Nat) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f a b,
    close <| mkApp3 Condition.bool.boolNatITE (mkApp2 f b₁ b₂)
      (add (add r r) one) (add r r))

/-- Validate a compiled well-founded recursion transactionally and retain its
closed, independently checked reduction certificate. -/
def unfoldNatWellFoundedCert (e : Expr) (fvs : Array Expr) (eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← M.sandbox (unfoldNatWellFoundedCore e fvs eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

/-- Compatibility projection used by equation-only primitive checks. -/
def unfoldNatWellFounded (e : Expr) (fvs : Array Expr) (eq_def : Expr)
    (fail : ∀ {α}, M α) : M Expr := do
  let some equation := natWellFoundedEquation e eq_def | fail
  _ ← unfoldNatWellFoundedCert e fvs eq_def fail
  return equation

def unfoldNatWellFoundedNat2Cert (e eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← withLocalDecl `m .default q(Nat) fun m =>
    withLocalDecl `n .default q(Nat) fun n =>
      M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

def unfoldNatWellFoundedBoolNat2Cert (e eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
    withLocalDecl `n .default q(Nat) fun n =>
      withLocalDecl `m .default q(Nat) fun m =>
        M.sandbox (unfoldNatWellFoundedCore e #[f, n, m] eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

structure NatGcdFixCertificate where
  core : NatWellFoundedCoreResult
  topLhs : Expr
  topRhs : Expr
  topProof : Expr
  zeroLhs : Expr
  zeroRhs : Expr
  zeroProofType : Expr
  succLhs : Expr
  succRhs : Expr
  succProofType : Expr
  succProof : Expr

private def natPair (a b : Expr) : Expr :=
  mkApp2 q(@PSigma.mk Nat (fun _ => Nat)) a b

def NatGcdFixCertificate.stateExpr (_r : NatGcdFixCertificate)
    (a b : Expr) : Expr :=
  mkApp2 q(@PSigma.mk Nat (fun _ => Nat)) a b

private def natGcdCall (gcd : Expr) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp2 gcd (.bvar 1) (.bvar 0)

def NatGcdFixCertificate.expectedTopLhs (_r : NatGcdFixCertificate)
    (gcd : Expr) : Expr := natGcdCall gcd

def NatGcdFixCertificate.expectedTopRhs (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkAppN r.core.goFn
    #[zero, zero, mkApp q(WellFounded.Nat.eager) (succ (.bvar 1)),
      r.stateExpr (.bvar 1) (.bvar 0), r.topProof]

def NatGcdFixCertificate.expectedZeroLhs (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 r.zeroProofType <|
    mkAppN go #[succ (.bvar 2), r.stateExpr zero (.bvar 1), .bvar 0]

def NatGcdFixCertificate.expectedZeroRhs (r : NatGcdFixCertificate) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 r.zeroProofType <| .bvar 1

def NatGcdFixCertificate.expectedSuccLhs (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  let sa := succ (.bvar 2)
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.succProofType <| mkAppN go
      #[succ (.bvar 3), r.stateExpr sa (.bvar 1), .bvar 0]

def NatGcdFixCertificate.expectedSuccRhs (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  let sa := succ (.bvar 2)
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.succProofType <| mkAppN go #[.bvar 3,
      r.stateExpr (mkApp2 q(Nat.mod) (.bvar 1) sa) sa, r.succProof]

def NatGcdFixCertificate.shape (r : NatGcdFixCertificate) (gcd : Expr) : Bool :=
  exprShapeEq r.topLhs (r.expectedTopLhs gcd) &&
  exprShapeEq r.topRhs r.expectedTopRhs &&
  exprShapeEq r.zeroLhs r.expectedZeroLhs &&
  exprShapeEq r.zeroRhs r.expectedZeroRhs &&
  exprShapeEq r.succLhs r.expectedSuccLhs &&
  exprShapeEq r.succRhs r.expectedSuccRhs

def specializeNatGcdFixCertificate (core : NatWellFoundedCoreResult)
    (fail : ∀ {α}, M α) : M NatGcdFixCertificate := do
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 core.goFn zero zero
  let topRhs ← withLambda core.callRhs fail fun m body =>
    withLambda body fail fun n body => do
      let args := body.getAppArgs
      unless body.getAppFn == core.fixGo && args.size == 7 do fail
      let .app eager _ := args[4]! | fail
      return (← getLCtx).mkLambda #[m, n]
        (mkAppN go #[mkApp eager (succ m), natPair m n, args[6]!])
  let topLhs := core.callLhs
  let (zeroLhs, zeroRhs) ← withLocalDecl `fuel .default q(Nat) fun fuel =>
    withLocalDecl `b .default q(Nat) fun b => do
      let stepR := mkApp3 core.specStepRhs zero zero fuel
      let state := natPair zero b
      let lhsFn := mkApp2 go (succ fuel) state
      let .forallE _ hpTy _ _ ← inferType lhsFn | fail
      withLocalDecl `hp .default hpTy fun hp => do
        let lhs := mkApp lhsFn hp
        _ ← whnfCore (mkApp (mkApp stepR state) hp)
        return ((← getLCtx).mkLambda #[fuel, b, hp] lhs,
          (← getLCtx).mkLambda #[fuel, b, hp] b)
  let (succLhs, succRhs) ← withLocalDecl `fuel .default q(Nat) fun fuel =>
    withLocalDecl `a .default q(Nat) fun a =>
      withLocalDecl `b .default q(Nat) fun b => do
        let sa := succ a
        let stepR := mkApp3 core.specStepRhs zero zero fuel
        let state := natPair sa b
        let lhsFn := mkApp2 go (succ fuel) state
        let .forallE _ hpTy _ _ ← inferType lhsFn | fail
        withLocalDecl `hp .default hpTy fun hp => do
          let lhs := mkApp lhsFn hp
          let rhs ← whnfCore (mkApp (mkApp stepR state) hp)
          let rhs ← unfoldDefinition rhs
          let rhs ← whnfCore rhs
          let rhs ← unfoldDefinition rhs
          let rhs ← whnfCore rhs
          let rhs ← rhs.withApp fun decCases args => do
            let .const ``Decidable.casesOn _ := decCases | fail
            unless args.size == 5 do fail
            let isFalse := args[3]!
            whnfCore (mkApp isFalse (mkApp q(Nat.succ_ne_zero) a))
          let args := rhs.getAppArgs
          unless rhs.getAppFn == core.fixGo && args.size == 7 do
            throw <| .other s!"invalid gcd recursive call: {rhs}"
          let recState := natPair (mkApp2 q(Nat.mod) b sa) sa
          let rhs := mkAppN go #[fuel, recState, args[6]!]
          return ((← getLCtx).mkLambda #[fuel, a, b, hp] lhs,
            (← getLCtx).mkLambda #[fuel, a, b, hp] rhs)
  let .lam _ _ (.lam _ _ topBody _) _ := topRhs | fail
  let topProof := topBody.getAppArgs[4]!
  let .lam _ _ (.lam _ _ (.lam _ zeroProofType _ _) _) _ := zeroLhs | fail
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ succProofType _ _) _) _) _ := succLhs | fail
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ succBody _) _) _) _ := succRhs | fail
  let succProof := succBody.getAppArgs[4]!
  return {
    core := core
    topLhs := topLhs
    topRhs := topRhs
    topProof := topProof
    zeroLhs := zeroLhs
    zeroRhs := zeroRhs
    zeroProofType := zeroProofType
    succLhs := succLhs
    succRhs := succRhs
    succProofType := succProofType
    succProof := succProof }

def checkNatGcdFixCertificate (core : NatWellFoundedCoreResult) (gcd : Expr)
    (fail : ∀ {α}, M α) : M NatGcdFixCertificate := do
  let cert ← M.sandbox (specializeNatGcdFixCertificate core fail)
  unless cert.shape gcd do
    throw <| .other "invalid Nat.gcd well-founded recursion certificate"
  checkNatWellFoundedCertificate cert.core
  checkNatWellFoundedEquation cert.topLhs cert.topRhs
  checkNatWellFoundedEquation cert.zeroLhs cert.zeroRhs
  checkNatWellFoundedEquation cert.succLhs cert.succRhs
  return cert

/-- The bitwise-specific part of a compiled well-founded certificate.  The
generic certificate proves that its equations are definitionally equal; this
wrapper additionally pins the candidate call, fuel, and pair-state shapes
needed by the semantic proof. -/
structure NatBitwiseFixCertificate where
  core : NatWellFoundedCoreResult
  callFn : Expr
  topLhs : Expr
  topRhs : Expr
  topProof : Expr
  zeroLhs : Expr
  zeroRhs : Expr
  zeroProofType : Expr
  zeroRightLhs : Expr
  zeroRightRhs : Expr
  zeroRightProofType : Expr
  succLhs : Expr
  succRhs : Expr
  succProofType : Expr
  succProof : Expr

def NatBitwiseFixCertificate.stateExpr (_r : NatBitwiseFixCertificate)
    (a b : Expr) : Expr := natPair a b

private def natBitwiseCall (bitwise : Expr) : Expr :=
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    mkApp3 bitwise (.bvar 2) (.bvar 1) (.bvar 0)

def NatBitwiseFixCertificate.expectedTopLhs
    (_r : NatBitwiseFixCertificate) (bitwise : Expr) : Expr :=
  natBitwiseCall bitwise

def NatBitwiseFixCertificate.expectedTopRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    mkAppN r.callFn #[.bvar 2,
      mkApp q(WellFounded.Nat.eager) (succ (.bvar 1)),
      .bvar 1, .bvar 0, r.topProof]

def NatBitwiseFixCertificate.expectedZeroLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroProofType <| mkAppN r.callFn
      #[.bvar 3, succ (.bvar 2), zero, .bvar 1, .bvar 0]

def NatBitwiseFixCertificate.expectedZeroRhs
    (_r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 _r.zeroProofType <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 (.bvar 3) q(false) q(true)) (.bvar 1) zero

def NatBitwiseFixCertificate.expectedZeroRightLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroRightProofType <| mkAppN r.callFn
      #[.bvar 3, succ (.bvar 2), succ (.bvar 1), zero, .bvar 0]

def NatBitwiseFixCertificate.expectedZeroRightRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroRightProofType <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 (.bvar 3) q(true) q(false)) (succ (.bvar 1)) zero

def NatBitwiseFixCertificate.expectedSuccLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let succ := mkApp q(Nat.succ)
  let sa := succ (.bvar 2)
  let sb := succ (.bvar 1)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 q(Nat) <| .lam0 r.succProofType <| mkAppN r.callFn
      #[.bvar 4, succ (.bvar 3), sa, sb, .bvar 0]

def NatBitwiseFixCertificate.expectedSuccRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let one := succ zero
  let two := succ one
  let add := mkApp2 q(Nat.add)
  let div := mkApp2 q(Nat.div)
  let mod := mkApp2 q(Nat.mod)
  let sa := succ (.bvar 2)
  let sb := succ (.bvar 1)
  let bit₁ := Condition.natEq.decide #[mod sa two, one]
  let bit₂ := Condition.natEq.decide #[mod sb two, one]
  let recursiveCall := mkAppN r.callFn #[.bvar 4, .bvar 3,
    div sa two, div sb two, r.succProof]
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 q(Nat) <| .lam0 r.succProofType <|
      mkApp3 Condition.bool.boolNatITE (mkApp2 (.bvar 4) bit₁ bit₂)
        (add (add recursiveCall recursiveCall) one)
        (add recursiveCall recursiveCall)

def NatBitwiseFixCertificate.shape
    (r : NatBitwiseFixCertificate) (bitwise : Expr) : Bool :=
  exprShapeEq r.topLhs (r.expectedTopLhs bitwise) &&
  exprShapeEq r.topRhs r.expectedTopRhs &&
  exprShapeEq r.zeroLhs r.expectedZeroLhs &&
  exprShapeEq r.zeroRhs r.expectedZeroRhs &&
  exprShapeEq r.zeroRightLhs r.expectedZeroRightLhs &&
  exprShapeEq r.zeroRightRhs r.expectedZeroRightRhs &&
  exprShapeEq r.succLhs r.expectedSuccLhs &&
  exprShapeEq r.succRhs r.expectedSuccRhs &&
  !r.callFn.hasFVar && !r.callFn.hasMVar

def specializeNatBitwiseFixCertificate (core : NatWellFoundedCoreResult)
    (fail : ∀ {α}, M α) : M NatBitwiseFixCertificate := do
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let callFn ← withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
    withLocalDecl `fuel .default q(Nat) fun fuel =>
      withLocalDecl `a .default q(Nat) fun a =>
        withLocalDecl `b .default q(Nat) fun b => do
          let go := mkAppN core.goFn #[f, a, b]
          let lhsFn := mkApp2 go fuel (natPair a b)
          let .forallE _ hpTy _ _ ← inferType lhsFn | fail
          withLocalDecl `hp .default hpTy fun hp =>
            return (← getLCtx).mkLambda #[f, fuel, a, b, hp] (mkApp lhsFn hp)
  let topRhs ← withLambda core.callRhs fail fun f body =>
    withLambda body fail fun n body =>
      withLambda body fail fun m body => do
        let args := body.getAppArgs
        unless body.getAppFn == core.fixGo && args.size == 7 do fail
        let .app eager _ := args[4]! | fail
        return (← getLCtx).mkLambda #[f, n, m]
          (mkAppN callFn #[f, mkApp eager (succ n), n, m, args[6]!])
  let .lam _ _ (.lam _ _ (.lam _ _ topBody _) _) _ := topRhs | fail
  let topProof := topBody.getAppArgs[4]!
  let (zeroLhs, zeroRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `b .default q(Nat) fun b => do
          let lhsFn := mkAppN callFn #[f, succ fuel, zero, b]
          let .forallE _ hpTy _ _ ← inferType lhsFn | fail
          withLocalDecl `hp .default hpTy fun hp =>
            return ((← getLCtx).mkLambda #[f, fuel, b, hp] (mkApp lhsFn hp),
              (← getLCtx).mkLambda #[f, fuel, b, hp] <|
                mkApp3 Condition.bool.boolNatITE
                  (mkApp2 f q(false) q(true)) b zero)
  let (zeroRightLhs, zeroRightRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `a .default q(Nat) fun a => do
          let sa := succ a
          let lhsFn := mkAppN callFn #[f, succ fuel, sa, zero]
          let .forallE _ hpTy _ _ ← inferType lhsFn | fail
          withLocalDecl `hp .default hpTy fun hp =>
            return ((← getLCtx).mkLambda #[f, fuel, a, hp] (mkApp lhsFn hp),
              (← getLCtx).mkLambda #[f, fuel, a, hp] <|
                mkApp3 Condition.bool.boolNatITE
                  (mkApp2 f q(true) q(false)) sa zero)
  let (succLhs, succRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `a .default q(Nat) fun a =>
          withLocalDecl `b .default q(Nat) fun b => do
            let sa := succ a
            let sb := succ b
            let lhsFn := mkAppN callFn #[f, succ fuel, sa, sb]
            let .forallE _ hpTy _ _ ← inferType lhsFn | fail
            withLocalDecl `hp .default hpTy fun hp => do
              let lhs := mkApp lhsFn hp
              let mut rhs := mkApp2
                (mkAppN core.specStepRhs #[f, sa, sb, fuel])
                (natPair sa sb) hp
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← rhs.withApp fun decCases args => do
                let .const ``Decidable.casesOn _ := decCases | fail
                unless args.size == 5 do fail
                whnfCore (mkApp args[3]! (mkApp q(Nat.succ_ne_zero) a))
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← rhs.withApp fun decCases args => do
                let .const ``Decidable.casesOn _ := decCases | fail
                unless args.size == 5 do fail
                whnfCore (mkApp args[3]! (mkApp q(Nat.succ_ne_zero) b))
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              let some recCall := (rhs.find? fun e =>
                let args := e.getAppArgs
                args.size == 2 && e.getAppFn.isLambda &&
                  (e.getAppFn.find? fun e' => e'.getAppFn == core.fixGo).isSome &&
                  (args[0]!.find? fun
                    | .const ``PSigma.mk _ => true
                    | _ => false).isSome) |
                throw <| .other "missing Nat.bitwise recursive call"
              let recCall ← whnfCore recCall
              let recArgs := recCall.getAppArgs
              unless recCall.getAppFn == core.fixGo && recArgs.size == 7 do fail
              let recProof := recArgs[6]!
              let one := succ zero
              let two := succ one
              let add := mkApp2 q(Nat.add)
              let div := mkApp2 q(Nat.div)
              let mod := mkApp2 q(Nat.mod)
              let bit₁ := Condition.natEq.decide #[mod sa two, one]
              let bit₂ := Condition.natEq.decide #[mod sb two, one]
              let recursiveCall := mkAppN callFn #[f, fuel,
                div sa two, div sb two, recProof]
              let canonicalRhs := mkApp3 Condition.bool.boolNatITE
                (mkApp2 f bit₁ bit₂)
                (add (add recursiveCall recursiveCall) one)
                (add recursiveCall recursiveCall)
              return ((← getLCtx).mkLambda #[f, fuel, a, b, hp] lhs,
                (← getLCtx).mkLambda #[f, fuel, a, b, hp] canonicalRhs)
  let zeroProofType := zeroLhs.bindingBody!.bindingBody!.bindingBody!
    |>.bindingDomain!
  let zeroRightProofType := zeroRightLhs.bindingBody!.bindingBody!.bindingBody!
    |>.bindingDomain!
  let succProofType := succLhs.bindingBody!.bindingBody!.bindingBody!
    |>.bindingBody! |>.bindingDomain!
  let some succCall := (succRhs.find? fun e =>
    e.getAppFn == callFn && e.getAppArgs.size == 5) | fail
  let succProof := succCall.getAppArgs[4]!
  return ⟨core, callFn, core.callLhs, topRhs, topProof,
    zeroLhs, zeroRhs, zeroProofType,
    zeroRightLhs, zeroRightRhs, zeroRightProofType,
    succLhs, succRhs, succProofType, succProof⟩

def checkNatBitwiseFixCertificate (core : NatWellFoundedCoreResult)
    (bitwise : Expr) (fail : ∀ {α}, M α) : M NatBitwiseFixCertificate := do
  let cert ← M.sandbox (specializeNatBitwiseFixCertificate core fail)
  unless cert.shape bitwise do
    throw <| .other "invalid Nat.bitwise well-founded recursion certificate"
  _ ← checkType cert.callFn
  checkNatWellFoundedCertificate cert.core
  checkNatWellFoundedEquation cert.topLhs cert.topRhs
  checkNatWellFoundedEquation cert.zeroLhs cert.zeroRhs
  checkNatWellFoundedEquation cert.zeroRightLhs cert.zeroRightRhs
  checkNatWellFoundedEquation cert.succLhs cert.succRhs
  return cert

/-- Expose one definitional reduction step of a validated compiled
well-founded definition underneath one lambda binder. -/
def reduceNatWellFoundedLam1 (e : Expr) (fail : ∀ {α}, M α) : M Expr :=
  withLambda e fail fun fv body => do
    let body ← whnfCore body
    let body ← unfoldDefinition body
    let body ← whnfCore body
    let body ← unfoldDefinition body
    let body ← whnfCore body
    return (← getLCtx).mkLambda #[fv] body

def reduceNatWellFoundedLam2 (e : Expr) (fail : ∀ {α}, M α) : M Expr :=
  withLambda e fail fun fv body => do
    let body ← reduceNatWellFoundedLam1 body fail
    return (← getLCtx).mkLambda #[fv] body

@[irreducible] def checkNatBitwiseZero
    (bitwise : Expr) (fail : ∀ {α}, M α) : M Unit := do
  let (lhs, rhs) := natBitwiseZeroEquation bitwise
  let lhs ← reduceNatWellFoundedLam2 lhs fail
  unless ← isDefEq lhs rhs do fail

def natModTopEquation (modFn : Expr) : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let mod := mkApp2 modFn
  let go := mkApp5 q(Nat.modCore.go)
  let c := Condition.natLE
  let x := .bvar 1
  let y := .bvar 0
  let sx := succ x
  let lhs := .lam0 q(Nat) <| .lam0 q(Nat) <| mod sx y
  let rhs := .lam0 q(Nat) <| .lam0 q(Nat) <|
    c.reflectedITE q(Nat) #[y, sx]
      (c.reflectedDITE #[q(Nat.succ Nat.zero), y]
        (go (.bvar 1) (.bvar 0) (succ (succ (.bvar 2)))
          (succ (.bvar 2))
          (mkApp q(Nat.lt_succ_self) (succ (.bvar 2))))
        (succ (.bvar 2))) sx
  (lhs, rhs)

def natModGoEquation : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let sub := mkApp2 q(Nat.sub)
  let le := mkApp2 q(@LE.le Nat _)
  let go := mkApp5 q(Nat.modCore.go)
  let c := Condition.natLE
  let y := .bvar 4
  let hy := .bvar 3
  let fuel := .bvar 2
  let x := .bvar 1
  let h := .bvar 0
  let close body := .lam0 q(Nat) <|
    .lam0 (le q(Nat.succ Nat.zero) (.bvar 0)) <|
    .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 (le (succ (.bvar 0)) (succ (.bvar 1))) body
  let lhs := close <| go y hy (succ fuel) x h
  let rhs := close <| c.reflectedDITE #[y, x]
    (go (.bvar 5) (.bvar 4) (.bvar 3)
      (sub (.bvar 2) (.bvar 5))
      (mkApp6 q(@Nat.div_rec_fuel_lemma)
        (.bvar 2) (.bvar 5) (.bvar 3) (.bvar 4)
        (.bvar 0) (.bvar 1)))
    (.bvar 2)
  (lhs, rhs)

def natDivTopRhs (x y : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let go := mkApp5 q(Nat.div.go)
  let c := Condition.natLE
  let x' := x.liftLooseBVars 0 1
  let y' := y.liftLooseBVars 0 1
  c.reflectedDITE #[q(Nat.succ Nat.zero), y]
    (go y' (.bvar 0) (succ x') x'
      (mkApp q(Nat.lt_succ_self) x')) q(Nat.zero)

def natDivTopEquation (divFn : Expr) : Expr × Expr :=
  let div := mkApp2 divFn
  let x := .bvar 1
  let y := .bvar 0
  let lhs := .lam0 q(Nat) <| .lam0 q(Nat) <| div x y
  let rhs := .lam0 q(Nat) <| .lam0 q(Nat) <|
    natDivTopRhs x y
  (lhs, rhs)

def natDivGoLhsBody (y hy fuel x h : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let go := mkApp5 q(Nat.div.go)
  go y hy (succ fuel) x h

def natDivGoRhsBody (y hy fuel x h : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let sub := mkApp2 q(Nat.sub)
  let go := mkApp5 q(Nat.div.go)
  let c := Condition.natLE
  c.reflectedDITE #[y, x]
    (succ (go (y.liftLooseBVars 0 1) (hy.liftLooseBVars 0 1)
      (fuel.liftLooseBVars 0 1)
      (sub (x.liftLooseBVars 0 1) (y.liftLooseBVars 0 1))
      (mkApp6 q(@Nat.div_rec_fuel_lemma)
        (x.liftLooseBVars 0 1) (y.liftLooseBVars 0 1)
        (fuel.liftLooseBVars 0 1) (hy.liftLooseBVars 0 1)
        (.bvar 0) (h.liftLooseBVars 0 1)))) q(Nat.zero)

def natDivGoEquation : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let le := mkApp2 q(@LE.le Nat _)
  let y := .bvar 4
  let hy := .bvar 3
  let fuel := .bvar 2
  let x := .bvar 1
  let h := .bvar 0
  let close body := .lam0 q(Nat) <|
    .lam0 (le q(Nat.succ Nat.zero) (.bvar 0)) <|
    .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 (le (succ (.bvar 0)) (succ (.bvar 1))) body
  let lhs := close <| natDivGoLhsBody y hy fuel x h
  let rhs := close <| natDivGoRhsBody y hy fuel x h
  (lhs, rhs)

def checkPrimitiveDef (v : DefinitionVal) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let tru := q(true)
  let fal := q(false)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let pred := mkApp q(Nat.pred)
  let add := mkApp2 q(Nat.add)
  let mul := mkApp2 q(Nat.mul)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let one := succ zero
  let two := succ one
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeqBool1 a b := isDefEq (.lam0 q(Bool) a) (.lam0 q(Bool) b)
  let x := .bvar 0
  let y := .bvar 1
  let env ← getEnv
  match v.name with
  | ``Nat.add =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- add : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let add := mkApp2 v.value
    -- add x 0 ≡ x
    unless ← defeq1 (add x zero) x do fail
    -- add y (succ x) ≡ succ (add y x)
    unless ← defeq2 (add y (succ x)) (succ (add y x)) do fail
  | ``Nat.pred =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- pred : Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat) do fail
    let pred := mkApp v.value
    unless ← isDefEq (pred zero) zero do fail
    unless ← defeq1 (pred (succ x)) x do fail
  | ``Nat.sub =>
    unless env.contains ``Nat.pred && v.levelParams.isEmpty do fail
    -- sub : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let sub := mkApp2 v.value
    unless ← defeq1 (sub x zero) x do fail
    unless ← defeq2 (sub y (succ x)) (pred (sub y x)) do fail
  | ``Nat.mul =>
    unless env.contains ``Nat.add && v.levelParams.isEmpty do fail
    -- mul : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let mul := mkApp2 v.value
    unless ← defeq1 (mul x zero) zero do fail
    unless ← defeq2 (mul y (succ x)) (add (mul y x) y) do fail
  | ``Nat.pow =>
    unless env.contains ``Nat.mul && v.levelParams.isEmpty do fail
    -- pow : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let pow := mkApp2 v.value
    unless ← defeq1 (pow x zero) one do fail
    unless ← defeq2 (pow y (succ x)) (mul (pow y x) y) do fail
  | ``Nat.mod =>
    unless env.contains ``Nat.sub && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- mod : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let mod := mkApp2 v.value
    unless ← defeq1 (mod zero x) zero do fail
    unless ← isDefEq (← checkType q(@LE.le Nat _)) q(Nat → Nat → Prop) do fail
    unless ← isDefEq (← checkType q(Nat.modCore.go))
      q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let c := Condition.natLE; c.check fail (ite := true) (dite := true)
    let (topL, topR) := natModTopEquation v.value
    _ ← checkType topR
    unless ← isDefEq topL topR do fail
    let (goL, goR) := natModGoEquation
    _ ← checkType goR
    unless ← isDefEq goL goR do fail
  | ``Nat.div =>
    unless env.contains ``Nat.sub && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- div : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let c := Condition.natLE; c.check fail (dite := true)
    unless ← isDefEq (← checkType q(@LE.le Nat _)) q(Nat → Nat → Prop) do fail
    unless ← isDefEq (← checkType q(Nat.div.go))
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let (topL, topR) := natDivTopEquation v.value
    _ ← checkType topR
    unless ← isDefEq topL topR do fail
    let (goL, goR) := natDivGoEquation
    _ ← checkType goR
    unless ← isDefEq goL goR do fail
  | ``Nat.gcd =>
    unless env.contains ``Nat.mod && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let gcdCore ← unfoldNatWellFoundedNat2Cert v.value
      q(type_of% Nat.gcd.eq_def) fail
    _ ← checkNatGcdFixCertificate gcdCore v.value fail
    let some gcd' := natWellFoundedEquation v.value q(type_of% Nat.gcd.eq_def) | fail
    unless ← isDefEq (← checkType gcd') q(Nat → Nat → Nat) do fail
    let gcd' := mkApp2 gcd'
    let gcd := mkApp2 v.value
    unless ← defeq1 (gcd' zero x) x do fail
    unless ← defeq2 (gcd' (succ y) x) (gcd (mod x (succ y)) (succ y)) do fail
    let gz₁ ← reduceNatWellFoundedLam1
      (.lam0 q(Nat) <| gcd zero (.bvar 0))
      fail
    unless ← isDefEq gz₁ (.lam0 q(Nat) <| .bvar 0) do fail
  | ``Nat.beq =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- beq : Nat → Nat → Bool
    unless ← isDefEq v.type q(Nat → Nat → Bool) do fail
    let beq := mkApp2 v.value
    unless ← isDefEq (beq zero zero) tru do fail
    unless ← defeq1 (beq zero (succ x)) fal do fail
    unless ← defeq1 (beq (succ x) zero) fal do fail
    unless ← defeq2 (beq (succ y) (succ x)) (beq y x) do fail
  | ``Nat.ble =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- ble : Nat → Nat → Bool
    unless ← isDefEq v.type q(Nat → Nat → Bool) do fail
    let ble := mkApp2 v.value
    unless ← isDefEq (ble zero zero) tru do fail
    unless ← defeq1 (ble zero (succ x)) tru do fail
    unless ← defeq1 (ble (succ x) zero) fal do fail
    unless ← defeq2 (ble (succ y) (succ x)) (ble y x) do fail
  | ``Nat.bitwise =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- bitwise : Nat → Nat → Nat
    unless ← isDefEq v.type q((Bool → Bool → Bool) → Nat → Nat → Nat) do fail
    let bitwiseCore ← unfoldNatWellFoundedBoolNat2Cert v.value
      q(type_of% Nat.bitwise.eq_def) fail
    _ ← checkNatBitwiseFixCertificate bitwiseCore v.value fail
    let some bitwise' := natWellFoundedEquation v.value
      q(type_of% Nat.bitwise.eq_def) | fail
    unless ← isDefEq (← checkType bitwise')
      q((Bool → Bool → Bool) → Nat → Nat → Nat) do fail
    let c := Condition.natEq; c.check fail (ite := true)
    let bc := Condition.bool; bc.check fail (ite := true)
    let e := natBitwiseEquation v.value
    _ ← checkType e
    unless ← isDefEq bitwise' e do fail
    let (z₁, z₂) := natBitwiseZeroEquation e
    unless ← isDefEq z₁ z₂ do fail
    let (zr₁, zr₂) := natBitwiseZeroRightEquation e
    unless ← isDefEq zr₁ zr₂ do fail
    let (s₁, s₂) := natBitwiseSuccEquation e v.value
    unless ← isDefEq s₁ s₂ do fail
    checkNatBitwiseZero v.value fail
  | ``Nat.land =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    let .app (.const ``Nat.bitwise []) and := v.value | fail
    -- land : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    unless ← isDefEq (← inferType and) q(Bool → Bool → Bool) do fail
    let and := mkApp2 and
    unless ← defeqBool1 (and fal x) fal do fail
    unless ← defeqBool1 (and tru x) x do fail
  | ``Nat.lor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    let .app (.const ``Nat.bitwise []) or := v.value | fail
    -- lor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    unless ← isDefEq (← inferType or) q(Bool → Bool → Bool) do fail
    let or := mkApp2 or
    unless ← defeqBool1 (or fal x) x do fail
    unless ← defeqBool1 (or tru x) tru do fail
  | ``Nat.xor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    let .app (.const ``Nat.bitwise []) xor := v.value | fail
    -- xor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    unless ← isDefEq (← inferType xor) q(Bool → Bool → Bool) do fail
    let xor := mkApp2 xor
    unless ← isDefEq (xor fal fal) fal do fail
    unless ← isDefEq (xor tru fal) tru do fail
    unless ← isDefEq (xor fal tru) tru do fail
    unless ← isDefEq (xor tru tru) fal do fail
  | ``Nat.shiftLeft =>
    unless env.contains ``Nat.mul && v.levelParams.isEmpty do fail
    -- shiftLeft : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let shl := mkApp2 v.value
    unless ← defeq1 (shl x zero) x do fail
    unless ← defeq2 (shl x (succ y)) (shl (mul two x) y) do fail
  | ``Nat.shiftRight =>
    unless env.contains ``Nat.div && v.levelParams.isEmpty do fail
    -- shiftRight : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let shr := mkApp2 v.value
    unless ← defeq1 (shr x zero) x do fail
    unless ← defeq2 (shr x (succ y)) (div (shr x y) two) do fail
  | ``Char.ofNat =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- Char : Type
    _ ← ensureType q(Char)
    -- @Char.ofNat : Nat → Char
    unless ← isDefEq v.type q(Nat → Char) do fail
  | ``String.ofList =>
    unless v.levelParams.isEmpty do fail
    -- Char : Type
    _ ← ensureType q(Char)
    -- List Char : Type
    _ ← ensureType q(List Char)
    -- @List.nil.{0} Char : List Char
    unless ← isDefEq (← checkType q(List.nil (α := Char))) q(List Char) do fail
    -- @List.cons.{0} Char : Char → List Char → List Char
    unless ← isDefEq (← checkType q(List.cons (α := Char))) q(Char → List Char → List Char) do fail
    -- String.ofList : List Char → String
    unless ← isDefEq v.type q(List Char → String) do fail
  | _ => return false
  return true

def checkPrimitiveInductive (_env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Except Exception Bool := do
  unless !isUnsafe && lparams.isEmpty && nparams == 0 do return false
  let [type] := types | return false
  unless type.type == .sort (.succ .zero) do return false
  let fail {α} : Except Exception α :=
    throw <| .other s!"invalid form for primitive inductive {type.name}"
  match type.name with
  | ``Bool =>
    let [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] := type.ctors | fail
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
      let (.true, _) ← Elab.Term.TermElabM.run (checkPrimitiveDef { v with })
        | throwError "{v.name}"
    | some (.inductInfo _) | some (.ctorInfo _) => pure ()
    | r => throwError "unexpected primitive: {r.map (·.name)}"
