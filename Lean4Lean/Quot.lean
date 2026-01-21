import Batteries.Tactic.OpenPrivate
import Lean4Lean.Environment.Basic
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Lean4Lean.LocalContext

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

abbrev ExprBuildT (m) := ReaderT LocalContext <| ReaderT NameGenerator m

def ExprBuildT.run [Monad m] (x : ExprBuildT m α) : m α := x {} {}

instance : MonadLocalNameGenerator (ExprBuildT m) where
  withFreshId x c ngen := x ngen.curr c ngen.next

def checkEqType (env : Environment) : Except Exception Unit := do
  let fail {α} (s : String) : Except Exception α :=
    throw <| .other s!"failed to initialize quot module, {s}"
  let .inductInfo info ← env.get ``Eq | fail "environment does not have 'Eq' type"
  let [u] := info.levelParams | fail "unexpected number of universe params at 'Eq' type"
  let [eqRefl] := info.ctors | fail "unexpected number of constructors for 'Eq' type"
  ExprBuildT.run do
    withLocalDecl `α .implicit (.sort (.param u)) fun α => do
      if info.type != ((← read).mkForall #[α] <| .arrow α <| .arrow α .prop) then
        fail "'Eq' has an expected type"
    let info ← env.get eqRefl
    let [u] := info.levelParams
      | fail "unexpected number of universe params at 'Eq' type constructor"
    withLocalDecl `α .implicit (.sort (.param u)) fun α => do
      withLocalDecl `a .default α fun a => do
        if info.type != ((← read).mkForall #[α, a] <| mkApp3 (.const ``Eq [.param u]) α a a) then
          fail "unexpected type for 'Eq' type constructor"

def Environment.addQuot (env : Environment) : Except Exception Environment := do
  if env.quotInit then return env
  checkEqType env
  ExprBuildT.run do
  let u := .param `u
  withLocalDecl `α .implicit (.sort u) fun α => do
  let env ← withLocalDecl `r .default (.arrow α (.arrow α .prop)) fun r => do
    -- constant Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
    let env := env.add <| .quotInfo {
      name := ``Quot, kind := .type, levelParams := [`u]
      type := (← read).mkForall #[α, r] <| .sort u
    }
    withLocalDecl `a .default α fun a => do
      -- constant Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
      return env.add <| .quotInfo {
        name := ``Quot.mk, kind := .ctor, levelParams := [`u]
        type := (← read).mkForall #[α, r, a] <| mkApp2 (.const ``Quot [u]) α r
      }
  withLocalDecl `r .implicit (.arrow α (.arrow α .prop)) fun r => do
  let quot_r := mkApp2 (.const ``Quot [u]) α r
  withLocalDecl `a .default α fun a => do
  let v := .param `v
  let env ← withLocalDecl `β .implicit (.sort v) fun β => do
    withLocalDecl `f .default (.arrow α β) fun f => do
    withLocalDecl `b .default α fun b => do
    let rab := mkApp2 r a b
    let fa_eq_fb := mkApp3 (.const ``Eq [v]) β (.app f a) (.app f b)
    let sanity := (← read).mkForall #[a, b] <| .arrow rab fa_eq_fb
    -- constant Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
    --   (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    return env.add <| .quotInfo {
      name := ``Quot.lift, kind := .lift, levelParams := [`u, `v]
      type := (← read).mkForall #[α, r, β, f] <| .arrow sanity <| .arrow quot_r β
    }
  let quotMk_a := mkApp3 (.const ``Quot.mk [u]) α r a
  withLocalDecl `β .implicit (.arrow quot_r .prop) fun β => do
  let all_quot := (← read).mkForall #[a] <| .app β quotMk_a
  withLocalDecl `q .implicit quot_r fun q => do
  -- constant Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop} :
  --   (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q */
  let env := env.add <| .quotInfo {
    name := ``Quot.ind, kind := .ind, levelParams := [`u]
    type := (← read).mkForall #[α, r, β] <|
      .forallE `mk all_quot ((← read).mkForall #[q] <| .app β q) .default
  }
  return markQuotInit env

def quotReduceRec [Monad m] (e : Expr) (whnf : Expr → m Expr) : m (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.getAppArgs
    if h : mkPos < args.size then
      let mk ← whnf args[mkPos]
      if !mk.isAppOfArity ``Quot.mk 3 then return none
      let mut r := Expr.app args[argPos]! mk.appArg!
      let elimArity := mkPos + 1
      if elimArity < args.size then
        r := mkAppRange r elimArity args.size args
      return some r
    else return none
  if fn == ``Quot.lift then cont 5 3
  else if fn == ``Quot.ind then cont 4 3
  else return none
