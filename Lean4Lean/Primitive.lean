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
    unless ← isDefEq (← inferType cond.prop) q(Nat → Nat → Prop) do fail
    reflect.check fail
    if ite then reflect.checkITE fail
    if dite then reflect.checkNatDITE fail
    let y := .bvar 0; let x := .bvar 1
    let e := .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
      (mkApp2 cond.prop x y) (mkApp2 asBool x y) (mkApp2 proof x y)
    _ ← checkType e
    unless ← isDefEq (← inferType asBool) q(Nat → Nat → Bool) do fail
    unless ← isProp (← inferType proof) do fail
    unless ← isDefEq e cond.dec do fail
  | .bool =>
    unless ← isDefEq (← inferType cond.prop) q(Bool → Prop) do fail
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

def checkPrimitiveDef (v : DefinitionVal) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let tru := q(true)
  let fal := q(false)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let pred := mkApp q(Nat.pred)
  let add := mkApp2 q(Nat.add)
  let sub := mkApp2 q(Nat.sub)
  let mul := mkApp2 q(Nat.mul)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let one := succ zero
  let two := succ one
  let defeq1 a b := isDefEq (.arrow q(Nat) a) (.arrow q(Nat) b)
  let defeq2 a b := defeq1 (.arrow q(Nat) a) (.arrow q(Nat) b)
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
    let le := mkApp2 q(@LE.le Nat _)
    unless ← isDefEq (← checkType q(Nat.modCore.go))
      q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let go := mkApp5 q(Nat.modCore.go)
    let c := Condition.natLE; c.check fail (ite := true) (dite := true)
    withLocalDecl `x .default q(Nat) fun x => do
    withLocalDecl `y .default q(Nat) fun y => do
    let sx := succ x
    let e := c.ite q(Nat) #[y, sx] (c.dite #[one, y]
      (go y (.bvar 0) (succ sx) sx (mkApp q(Nat.lt_succ_self) sx)) sx) sx
    _ ← checkType e
    unless ← isDefEq (mod sx y) e do fail
    withLocalDecl `hy .default (le one y) fun hy => do
    withLocalDecl `fuel .default q(Nat) fun fuel => do
    withLocalDecl `h .default (le (succ x) (succ fuel)) fun h => do
    let e := c.dite #[y, x] (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x
    _ ← checkType e
    unless ← isDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.div =>
    unless env.contains ``Nat.sub && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- div : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let div := mkApp2 v.value
    let c := Condition.natLE; c.check fail (dite := true)
    unless ← isDefEq (← checkType q(@LE.le Nat _)) q(Nat → Nat → Prop) do fail
    let le := mkApp2 q(@LE.le Nat _)
    unless ← isDefEq (← checkType q(Nat.div.go))
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let go := mkApp5 q(Nat.div.go)
    withLocalDecl `x .default q(Nat) fun x => do
    withLocalDecl `y .default q(Nat) fun y => do
    let e := c.dite #[one, y] (go y (.bvar 0) (succ x) x (mkApp q(Nat.lt_succ_self) x)) zero
    _ ← checkType e
    unless ← isDefEq (div x y) e do fail
    withLocalDecl `hy .default (le one y) fun hy => do
    withLocalDecl `fuel .default q(Nat) fun fuel => do
    withLocalDecl `h .default (le (succ x) (succ fuel)) fun h => do
    let e := c.dite #[y, x] (succ (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) zero
    _ ← checkType e
    unless ← isDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.gcd =>
    unless env.contains ``Nat.mod && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    withLocalDecl `m .default q(Nat) fun m => do
    withLocalDecl `n .default q(Nat) fun n => do
    let gcd' ← unfoldWellFounded v.value #[m, n] q(type_of% Nat.gcd.eq_def) fail
    let gcd' := mkApp2 gcd'
    let gcd := mkApp2 v.value
    unless ← isDefEq (gcd' zero m) m do fail
    unless ← isDefEq (gcd' (succ n) m) (gcd (mod m (succ n)) (succ n)) do fail
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
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f => do
    withLocalDecl `n .default q(Nat) fun n => do
    withLocalDecl `m .default q(Nat) fun m => do
    let bitwise' ← unfoldWellFounded v.value #[f, n, m] q(type_of% Nat.bitwise.eq_def) fail
    let bitwise := mkApp3 v.value
    let c := Condition.natEq; c.check fail (ite := true)
    let bc := Condition.bool; bc.check fail (ite := true)
    let e :=
      c.ite q(Nat) #[n, zero] (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
      c.ite q(Nat) #[m, zero] (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
      let n' := div n two
      let m' := div m two
      let b₁ := c.decide #[mod n two, one]
      let b₂ := c.decide #[mod m two, one]
      let r := bitwise f n' m'
      bc.ite q(Nat) #[mkApp2 f b₁ b₂] (add (add r r) one) (add r r)
    _ ← checkType e
    unless ← isDefEq (mkApp3 bitwise' f n m) e do fail
  | ``Nat.land =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- land : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) and := v.value | fail
    let and := mkApp2 and
    unless ← defeq1 (and fal x) fal do fail
    unless ← defeq1 (and tru x) x do fail
  | ``Nat.lor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- lor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) or := v.value | fail
    let or := mkApp2 or
    unless ← defeq1 (or fal x) x do fail
    unless ← defeq1 (or tru x) tru do fail
  | ``Nat.xor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- xor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) xor := v.value | fail
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
