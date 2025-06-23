import Lean4Lean.TypeChecker
import Lean4Lean.Environment.Basic

namespace Lean4Lean
namespace Environment
open Lean hiding Environment Exception
open Kernel TypeChecker

open private Lean.Kernel.Environment.add from Lean.Environment

def lam0 (ty e) := Expr.lam `_ ty e default

def unfoldWellFounded (e : Expr) (args : List Expr) (eq_def : Name) (fail : ∀ {α}, M α) : M Expr :=
  match args with
  | ty :: xs =>
    withLocalDecl `n ty .default fun n => do
    let rhs ← unfoldWellFounded (.app e n) xs eq_def fail
    return (← getLCtx).mkLambda #[n] rhs
  | [] =>
    e.withApp fun e args => do
    let .const _ us := e | fail
    let .app _ rhs ← checkType (mkAppN (.const eq_def us) args) | fail
    let .app e1 wfn ← whnf e | fail
    e1.withApp fun accRec args => do
    let #[α,r,_,_,n] := args | fail
    let .const ``Acc.rec [_, u] := accRec | fail
    let .app wf _ := wfn | fail
    let L := lam0 α <| lam0 (mkApp2 r (.bvar 0) n) (mkApp wf (.bvar 1))
    let wfn' := mkApp4 (.const ``Acc.intro [u]) α r n L
    let p ← inferType wfn
    unless ← isProp p do fail
    unless ← isDefEq p (← checkType wfn') do fail
    unless ← isDefEq (e1.app wfn') rhs do fail
    pure rhs

deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for MVarId
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for String.Pos
deriving instance ToExpr for Substring
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
  type := q(fun p b => (b = true → p) ∧ (¬b = true → ¬p))
  ofTrue := q(fun p (H : (true = true → p) ∧ (¬true = true → ¬p)) => H.1 rfl)
  ofFalse := q(fun p (H : (false = true → p) ∧ (¬false = true → ¬p)) => H.2 Bool.noConfusion)
  toDec := q(fun p b (H : (b = true → p) ∧ (¬b = true → ¬p)) =>
    if h : b = true then isTrue (H.1 h) else isFalse (H.2 h))

def Reflection.defn₂ : Reflection where
  type := q(fun p b => (b = true → p) ∧ (b = false → ¬p))
  ofTrue := q(fun p (H : (true = true → p) ∧ (true = false → ¬p)) => H.1 rfl)
  ofFalse := q(fun p (H : (false = true → p) ∧ (false = false → ¬p)) => H.2 rfl)
  toDec := q(fun p b (H : (b = true → p) ∧ (b = false → ¬p)) =>
    b.casesOn (motive := fun b' => b = b' → Decidable p)
      (fun h => isFalse (H.2 h)) (fun h => isTrue (H.1 h)) rfl)

def Reflection.check (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.type) (.arrow .prop (.arrow (.const ``Bool []) .prop)) do fail

structure Condition where
  prop : Expr
  dec : Expr
  asBool : Expr
  reflect : Reflection
  proof : Expr

def Condition.le : Condition where
  prop := q(@LE.le Nat _)
  dec := q(Nat.decLe)
  asBool := q(Nat.ble)
  reflect := .defn₁
  proof := q(fun n m => And.intro (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))

def Condition.eq : Condition where
  prop := q(@Eq Nat)
  dec := q(Nat.decEq)
  asBool := q(Nat.beq)
  reflect := .defn₂
  proof := q(fun n m => And.intro (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m))

def Condition.check (cond : Condition) (fail : ∀ {α}, M α) : M Unit := do
  cond.reflect.check fail
  let y := .bvar 0; let x := .bvar 1
  let e := lam0 q(Nat) <| lam0 q(Nat) <| mkApp3 cond.reflect.toDec
    (mkApp2 cond.prop x y) (mkApp2 cond.asBool x y) (mkApp2 cond.proof x y)
  _ ← checkType e
  _ ← checkType cond.dec
  unless ← isDefEq (← inferType cond.prop) q(Nat → Nat → Prop) do fail
  unless ← isDefEq (← inferType cond.asBool) q(Nat → Nat → Bool) do fail
  unless ← isProp (← inferType cond.proof) do fail
  unless ← isDefEq e cond.dec do fail

def Reflection.natITE (r : Reflection) : Expr :=
  lam0 q(Prop) <| lam0 q(Bool) <| lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    mkApp2 q(@ite Nat) (.bvar 2) (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0))

def Reflection.natDITE (r : Reflection) : Expr :=
  lam0 q(Prop) <| lam0 q(Bool) <| lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    mkApp2 q(@dite Nat) (.bvar 2) (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0))

def Reflection.checkNatITE (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.natITE) (.arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(Nat → Nat → Nat)) do fail
  withLocalDecl `p q(Prop) .default fun p => do
  withLocalDecl `H (mkApp2 r.type p q(true)) .default fun H => do
    unless ← isDefEq (mkApp3 r.natITE p q(true) H) q(fun a _ : Nat => a) do fail
  withLocalDecl `H (mkApp2 r.type p q(false)) .default fun H => do
    unless ← isDefEq (mkApp3 r.natITE p q(false) H) q(fun _ a : Nat => a) do fail

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
  withLocalDecl `p q(Prop) .default fun p => do
  withLocalDecl `a (.arrow p q(Nat)) .default fun a => do
  withLocalDecl `b (.arrow (mkApp q(Not) p) q(Nat)) .default fun b => do
  withLocalDecl `H (mkApp2 r.type p q(true)) .default fun H => do
    unless ← isDefEq (mkApp5 r.natDITE p q(true) H a b) (mkApp a (mkApp2 r.ofTrue p H)) do fail
  withLocalDecl `H (mkApp2 r.type p q(false)) .default fun H => do
    unless ← isDefEq (mkApp5 r.natDITE p q(false) H a b) (mkApp b (mkApp2 r.ofFalse p H)) do fail

protected def Condition.ite (cond : Condition) (a b t e : Expr) : Expr :=
  mkApp4 q(@ite Nat) (mkApp2 cond.prop a b) (mkApp2 cond.dec a b) t e

protected def Condition.dite (cond : Condition) (a b t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkApp2 cond.prop a b) (mkApp2 cond.dec a b)
    (lam0 (mkApp2 cond.prop a b) t)
    (lam0 (mkApp q(Not) (mkApp2 cond.prop a b)) e)

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
  let gcd := mkApp2 q(Nat.gcd)
  let two := succ (succ zero)
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
    unless ← defeq1 (pow x zero) (succ zero) do fail
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
    let c := Condition.le; c.check fail
    c.reflect.checkNatITE fail; c.reflect.checkNatDITE fail
    withLocalDecl `x q(Nat) .default fun x => do
    withLocalDecl `y q(Nat) .default fun y => do
    let sx := succ x
    let e := c.ite y sx (c.dite (succ zero) y
      (go y (.bvar 0) (succ sx) sx (mkApp q(Nat.lt_succ_self) sx)) sx) sx
    _ ← checkType e
    unless ← isDefEq (mod sx y) e do fail
    withLocalDecl `hy (le (succ zero) y) .default fun hy => do
    withLocalDecl `fuel q(Nat) .default fun fuel => do
    withLocalDecl `h (le (succ x) (succ fuel)) .default fun h => do
    let e := c.dite y x (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)) x
    _ ← checkType e
    unless ← isDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.div =>
    unless env.contains ``Nat.sub && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- div : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let div := mkApp2 v.value
    let c := Condition.le; c.check fail; c.reflect.checkNatDITE fail
    unless ← isDefEq (← checkType q(@LE.le Nat _)) q(Nat → Nat → Prop) do fail
    let le := mkApp2 q(@LE.le Nat _)
    unless ← isDefEq (← checkType q(Nat.div.go))
      q(∀ y, Nat.succ Nat.zero ≤ y → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
    let go := mkApp5 q(Nat.div.go)
    withLocalDecl `x q(Nat) .default fun x => do
    withLocalDecl `y q(Nat) .default fun y => do
    let e := c.dite (succ zero) y (go y (.bvar 0) (succ x) x (mkApp q(Nat.lt_succ_self) x)) zero
    _ ← checkType e
    unless ← isDefEq (div x y) e do fail
    withLocalDecl `hy (le (succ zero) y) .default fun hy => do
    withLocalDecl `fuel q(Nat) .default fun fuel => do
    withLocalDecl `h (le (succ x) (succ fuel)) .default fun h => do
    let e := c.dite y x (succ (go y hy fuel (sub x y)
      (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h))) zero
    _ ← checkType e
    unless ← isDefEq (go y hy (succ fuel) x h) e do fail
  | ``Nat.gcd =>
    unless env.contains ``Nat.mod && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let gcd' ← unfoldWellFounded (.const ``Nat.gcd []) [q(Nat), q(Nat)] ``Nat.gcd.eq_def fail
    let gcd' := mkApp2 gcd'
    unless ← defeq1 (gcd' zero x) x do fail
    unless ← defeq2 (gcd' (succ y) x) (gcd (mod x (succ y)) (succ y)) do fail
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
    return true -- TODO
  | ``Nat.land =>
    unless env.contains ``Nat.bitwise && env.contains ``and && v.levelParams.isEmpty do fail
    -- land : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) and := v.value | fail
    let and := mkApp2 and
    unless ← defeq1 (and fal x) fal do fail
    unless ← defeq1 (and tru x) x do fail
  | ``Nat.lor =>
    unless env.contains ``Nat.bitwise && env.contains ``or && v.levelParams.isEmpty do fail
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
  | _ => return false
  return true

def checkPrimitiveInductive (env : Environment) (lparams : List Name) (nparams : Nat)
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
  | ``String =>
    let [⟨``String.mk,
      .forallE _ (.app (.const ``List [.zero]) (.const ``Char [])) (.const ``String []) _
    ⟩] := type.ctors | fail
    M.run env (safety := .safe) (lctx := {}) do
      -- We need the following definitions for `strLitToConstructor` to work:
      -- Nat : Type (this is primitive so checking for existence suffices)
      let nat := .const ``Nat []
      unless env.contains ``Nat do fail
      -- Char : Type
      let char := .const ``Char []
      _ ← ensureType char
      -- List Char : Type
      let listchar := mkApp (.const ``List [.zero]) char
      _ ← ensureType listchar
      -- @List.nil.{0} Char : List Char
      let listNil := .app (.const ``List.nil [.zero]) char
      unless ← isDefEq (← check listNil []) listchar do fail
      -- @List.cons.{0} Char : List Char
      let listCons := .app (.const ``List.cons [.zero]) char
      unless ← isDefEq (← check listCons [])
        (.arrow char (.arrow listchar listchar)) do fail
      -- String.mk : List Char → String (already checked)
      -- @Char.ofNat : Nat → Char
      let charOfNat := .const ``Char.ofNat []
      unless ← isDefEq (← check charOfNat []) (.arrow nat char) do fail
  | _ => return false
  return true
