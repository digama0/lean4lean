/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Lean.Environment

namespace Lean

def HashMap.keyNameSet (m : Std.HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}

namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  -- Replay needs dependencies from theorem proofs and opaque bodies even though
  -- `ConstantInfo.value?` hides both by default.
  c.type.getUsedConstants' ++ match c.value? (allowOpaque := true) with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

end Lean

def Lean.Kernel.Exception.mapEnvM [Monad m]
    (ex : Exception) (f : Environment → m Environment) : m Exception := do
  match ex with
  | unknownConstant env c => return .unknownConstant (← f env) c
  | alreadyDeclared env c => return .alreadyDeclared (← f env) c
  | declTypeMismatch env d t => return .declTypeMismatch env d t
  | declHasMVars env c e => return declHasMVars (← f env) c e
  | declHasFVars env c e => return declHasFVars (← f env) c e
  | funExpected env lctx e => return funExpected (← f env) lctx e
  | typeExpected env lctx e => return typeExpected (← f env) lctx e
  | letTypeMismatch  env lctx n t1 t2 => return letTypeMismatch (← f env) lctx n t1 t2
  | exprTypeMismatch env lctx e t => return exprTypeMismatch (← f env) lctx e t
  | appTypeMismatch  env lctx e fn arg => return appTypeMismatch (← f env) lctx e fn arg
  | invalidProj env lctx e => return invalidProj (← f env) lctx e
  | thmTypeIsNotProp env c t => return thmTypeIsNotProp (← f env) c t
  | other _
  | deterministicTimeout
  | excessiveMemory
  | deepRecursion
  | interrupted => return ex

def Lean.Declaration.name : Declaration → String
  | .axiomDecl d => s!"axiomDecl {d.name}"
  | .defnDecl d => s!"defnDecl {d.name}"
  | .thmDecl d => s!"thmDecl {d.name}"
  | .opaqueDecl d => s!"opaqueDecl {d.name}"
  | .quotDecl => s!"quotDecl"
  | .mutualDefnDecl d => s!"mutualDefnDecl {d.map (·.name)}"
  | .inductDecl _ _ d _ => s!"inductDecl {d.map (·.name)}"

def Lean.Expr.hasStrLit (e : Expr) : Bool := e.findAny isStringLit

def Lean.ConstantInfo.hasStrLit (ci : ConstantInfo) : Bool :=
  ci.type.hasStrLit || (ci.value? (allowOpaque := true)).any (·.hasStrLit)

open Lean hiding Environment Exception
open Kernel

namespace Lean4Lean.Replay

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal
deriving instance BEq for QuotKind
deriving instance BEq for QuotVal
deriving instance BEq for InductiveVal
deriving instance BEq for ConstantInfo

/-! ### The replay core

The core walks the source constants in dependency order, rebuilds a `Declaration` from each
`ConstantInfo`, sends it to the verified kernel (`Lean4Lean.addDecl`), and finally runs the
comparisons against the source. It is written over an arbitrary monad `m`, whose only role is to
run the `Hooks` (logging, timing, comparison with the C++ kernel) around each `addDecl`; the pure
instance is `replayPure` (`m := Except ReplayError`, no hooks), and the executable runs the same
definition at `m := ExceptT ReplayError IO`.

Soundness is carried by types: the state records a proof (`Replayed`) that its environment is
obtained from the start environment by successful `addDecl` calls, and the result
(`ReplayResult`) records the outcome of the final agreement check. Hence every value the core
returns, in any monad, satisfies the theorems of `Lean4Lean.Verify.Replay`, without unfolding the
(partial) dependency walk. -/

/-- Configuration of the replay core: the source constant table and the kernel fuel. -/
structure Config where
  /-- The constants of the source environment, to be replayed. -/
  newConstants : Std.HashMap Name ConstantInfo
  /-- Whether to check at the end that the quotient module is initialized. -/
  checkQuot := true
  /-- The fuel passed to every `Lean4Lean.addDecl` call. -/
  fuel : Lean4Lean.FuelConfig := {}

/-- Errors reported by the replay core. The IO wrapper turns them into the messages of
`IO.userError`. -/
inductive ReplayError where
  /-- The kernel rejected a declaration while replaying the constant `name`. -/
  | kernel (name : Name) (ex : Kernel.Exception)
  /-- Any other failure, with its message. -/
  | msg (msg : String)

instance : Inhabited ReplayError := ⟨.msg "unreachable"⟩

/-! ### The type of `Eq`

Quotient initialization (`quotDecl`) types `Quot.lift` against `Eq`. The kernel's `checkEqType`
compares the type of `Eq` with the prelude's (up to `Expr.eqv`) but does not look at the safety
of `Eq`, and the abstract model of `Quot.lift` needs `Eq` in the safe model. So the driver
additionally requires, before the step that initializes the quotient module, that `Eq` is a safe
constant with one universe parameter whose type is `==` to the prelude's
(`HasCanonicalEqType` in `Lean4Lean/Verify/Replay.lean`). Nothing is required of `Eq.refl` or
`Eq.rec`: the abstract model of `quotDecl` does not mention them. -/

namespace PreludeEq

/-- The type of `Eq` as `Init.Prelude` declares it. `==` ignores the binder names and binder
annotations. -/
def eqType (u alpha lhs rhs : Name) : Expr :=
  .forallE alpha (.sort (.param u))
    (.forallE lhs (.bvar 0)
      (.forallE rhs (.bvar 1) (.sort .zero) .default) .default)
    .implicit

def isSafe (ci : ConstantInfo) : Bool := !ci.isUnsafe && !ci.isPartial

end PreludeEq

/-- `Eq` is a safe constant of `env` with one universe parameter `u`, whose type is `==` to the
prelude's type of `Eq.{u}`. -/
def hasCanonicalEqType (env : Environment) : Bool :=
  match env.find? ``Eq with
  | some ci => PreludeEq.isSafe ci && match ci.levelParams with
    | [u] => ci.type == PreludeEq.eqType u `α `a `b
    | _ => false
  | none => false

/-- `env` is obtained from an environment satisfying `Start` by successful checked additions
`Lean4Lean.addDecl · d (check := true) (fuel := fuel)`; a step that initializes the quotient
module is taken only when `Eq` is safe with the prelude's type (`hasCanonicalEqType`). -/
inductive Replayed (fuel : Lean4Lean.FuelConfig) (Start : Environment → Prop) :
    Environment → Prop where
  | start : Start env → Replayed fuel Start env
  | step : Replayed fuel Start env → Lean4Lean.addDecl env d true fuel = .ok env' →
    (d = .quotDecl → env.quotInit = false → hasCanonicalEqType env = true) →
    Replayed fuel Start env'

/-- Callbacks run around each `addDecl` call of the core. They cannot change the replay
state. -/
structure Hooks (m : Type → Type) where
  /-- Run before each `addDecl`; its result is passed to `afterAdd`. -/
  beforeAdd : Declaration → m Nat
  /-- Run after each successful `addDecl`, with the name of the constant being replayed, the
  declaration, the environments before and after, and the value returned by `beforeAdd`. -/
  afterAdd : Name → Declaration → Environment → Environment → Nat → m Unit

/-- No hooks. -/
def Hooks.none [Pure m] : Hooks m where
  beforeAdd _ := pure 0
  afterAdd _ _ _ _ _ := pure ()

/-- The state of the replay core. -/
structure State (fuel : Lean4Lean.FuelConfig) (Start : Environment → Prop) where
  env : Environment
  /-- `env` is reached from the start environment by successful `addDecl` calls. -/
  replayed : Replayed fuel Start env
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  numAdded : Nat := 0
  hasStrings := false

/-- The monad of the replay core. -/
abbrev CoreM (m : Type → Type) (fuel : Lean4Lean.FuelConfig) (Start : Environment → Prop) :=
  StateT (State fuel Start) m

instance [Monad m] [MonadExceptOf ReplayError m] :
    Inhabited (CoreM m fuel Start α) := ⟨throw (.msg "unreachable")⟩

section Core
variable {m : Type → Type} [Monad m] [MonadExceptOf ReplayError m]
  (hooks : Hooks m) (cfg : Config) {Start : Environment → Prop}

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : CoreM m cfg.fuel Start Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Add a declaration with the verified kernel, while replaying the constant `name`. Quotient
initialization additionally requires a safe `Eq` with the prelude's type
(`hasCanonicalEqType`). -/
def addDecl (name : Name) (d : Declaration) : CoreM m cfg.fuel Start Unit := do
  let s ← get
  let eqOk : Bool := match d with
    | .quotDecl => s.env.quotInit || hasCanonicalEqType s.env
    | _ => true
  if hq : eqOk = true then
    let t ← hooks.beforeAdd d
    match h : Lean4Lean.addDecl s.env d true (fuel := cfg.fuel) with
    | .ok env =>
      hooks.afterAdd name d s.env env t
      set { s with
        env, numAdded := s.numAdded + 1
        replayed := .step s.replayed h fun hd hi => by subst hd; simpa [eqOk, hi] using hq }
    | .error ex => throw (ReplayError.kernel name ex)
  else
    throw (ReplayError.msg
      s!"at {name}: initializing the quotient module needs a safe Eq with the prelude's type")

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : CoreM m cfg.fuel Start Unit := do
  if ← isTodo cfg name then
    let some ci := cfg.newConstants[name]?
      | throw (ReplayError.msg s!"unreachable: {name} is not a source constant")
    let mut usedConstants := ci.getUsedConstants
    -- We want `String.ofList` to be available when encountering string literals.
    -- Presumably faster to first check if we already have it, before traversing
    -- the declaration
    unless (← get).hasStrings do
      if ci.hasStrLit then
        usedConstants := usedConstants.insert ``String.ofList
        usedConstants := usedConstants.insert ``Char.ofNat
        modify ({· with hasStrings := true })
    replayConstants usedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      let addDeclAt (d : Declaration) := addDecl hooks cfg name d
      match ci with
      | .defnInfo   info => addDeclAt (.defnDecl   info)
      | .thmInfo    info => addDeclAt (.thmDecl    info)
      | .axiomInfo  info => addDeclAt (.axiomDecl  info)
      | .opaqueInfo info => addDeclAt (.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all := info.all.map fun n => cfg.newConstants[n]!
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo := all.map fun ci =>
          (ci, ci.inductiveVal!.ctors.map fun n => cfg.newConstants[n]!)
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDeclAt (.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        replayConstant ``Eq
        addDeclAt .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : CoreM m cfg.fuel Start Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : CoreM m cfg.fuel Start Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, cfg.newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      unless info == info' do throw (ReplayError.msg s!"Invalid constructor {ctor}")
    | _, _ => throw (ReplayError.msg s!"No such constructor {ctor}")

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : CoreM m cfg.fuel Start Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, cfg.newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      unless info == info' do throw (ReplayError.msg s!"Invalid recursor {ctor}")
    | _, _ => throw (ReplayError.msg s!"No such recursor {ctor}")

/--
Check that at the end of (any) file, the quotient module is initialized by the end.
(It will already be initialized at the beginning, unless this is the very first file,
`Init.Core`, which is responsible for initializing it.)
This is needed because it is an assumption in `finalizeImport`.
-/
def checkQuotInit : CoreM m cfg.fuel Start Unit := do
  unless (← get).env.quotInit do
    throw (ReplayError.msg s!"initial import (Init.Prelude) didn't initialize quotient module")

end Core

/-- The names of the source constants the driver replays: everything except unsafe and partial
constants (which it skips; later we may want to handle partial constants). -/
def safeNames (src : Std.HashMap Name ConstantInfo) : List Name :=
  src.toList.filterMap fun (n, ci) => if !ci.isUnsafe && !ci.isPartial then some n else none

theorem mem_safeNames {src : Std.HashMap Name ConstantInfo} {n : Name} {ci : ConstantInfo}
    (h : src[n]? = some ci) (hu : ci.isUnsafe = false) (hp : ci.isPartial = false) :
    n ∈ safeNames src := by
  simp only [safeNames, List.mem_filterMap]
  exact ⟨(n, ci), Std.HashMap.mem_toList_iff_getElem?_eq_some.2 h, by simp [hu, hp]⟩

/-- The final agreement check: the first name of `names` whose constant in `env` is missing or
differs (under `==`, which compares expressions with `Expr.eqv`) from the source constant. -/
def agreementError? (src : Std.HashMap Name ConstantInfo) (env : Environment) :
    List Name → Option ReplayError
  | [] => none
  | n :: ns =>
    match env.find? n, src[n]? with
    | some ci', some ci =>
      if ci' == ci then agreementError? src env ns
      else some (.msg s!"Replayed constant {n} differs from the source")
    | _, _ => some (.msg s!"Replayed constant {n} is missing")

theorem agreementError?_eq_none {src : Std.HashMap Name ConstantInfo} {env : Environment} :
    ∀ {names : List Name}, agreementError? src env names = none →
      ∀ n ∈ names, ∀ ci, src[n]? = some ci →
        ∃ ci', env.find? n = some ci' ∧ (ci' == ci) = true
  | [], _, n, hn, _, _ => by simp at hn
  | n :: ns, h, n', hn', ci, hci => by
    simp only [agreementError?] at h
    split at h
    · rename_i ci₁ ci₂ h₁ h₂
      split at h
      · rename_i heq
        rcases List.mem_cons.1 hn' with rfl | hn'
        · exact ⟨ci₁, h₁, by rw [h₂] at hci; cases hci; exact heq⟩
        · exact agreementError?_eq_none h n' hn' ci hci
      · cases h
    · cases h

/-- The outcome of a successful replay of the source constants `cfg.newConstants` into `start`
(replaying only the dependency cone of `decl` if it is `some`). The replay of a target `d` fails
unless `d` is a safe, non-partial source constant, and then `d` itself is checked. -/
structure ReplayResult (cfg : Config) (start : Environment) (decl : Option Name) where
  /-- The final environment. -/
  env : Environment
  /-- The number of `addDecl` calls. -/
  numAdded : Nat
  /-- The constants compared with the source by the final agreement check. -/
  checked : List Name
  /-- `env` is obtained from `start` by successful checked `addDecl` calls with `cfg.fuel`. -/
  replayed : Replayed cfg.fuel (· = start) env
  /-- Every checked constant is present in `env` and agrees with the source constant. -/
  agree : ∀ n ∈ checked, ∀ ci, cfg.newConstants[n]? = some ci →
    ∃ ci', env.find? n = some ci' ∧ (ci' == ci) = true
  /-- Without `decl`, every safe, non-partial source constant is checked. -/
  complete : decl = none → ∀ n ci, cfg.newConstants[n]? = some ci →
    ci.isUnsafe = false → ci.isPartial = false → n ∈ checked
  /-- With `decl := some d`, the target `d` is a source constant and is checked. -/
  target : ∀ d, decl = some d → d ∈ checked ∧ ∃ ci, cfg.newConstants[d]? = some ci

/-- The replay core: replay the source constants `cfg.newConstants` into `env`, sending them to
the verified kernel, then compare the generated constructors and recursors with the source's,
check quotient initialization (if `cfg.checkQuot`), and finally check that every replayed
constant is present and agrees with the source. With `decl := some d` only the dependency cone of
`d` is replayed; it is an error if `d` is not a safe, non-partial source constant. -/
def replayCore {m : Type → Type} [Monad m] [MonadExceptOf ReplayError m]
    (hooks : Hooks m) (cfg : Config) (env : Environment) (decl : Option Name := none) :
    m (ReplayResult cfg env decl) := do
  let allSafe := safeNames cfg.newConstants
  if let some d := decl then
    match cfg.newConstants[d]? with
    | none => throw (ReplayError.msg s!"target {d} is not a source constant")
    | some ci =>
      if ci.isUnsafe || ci.isPartial then
        throw (ReplayError.msg s!"target {d} is unsafe or partial and is not replayed")
  let remaining : NameSet := allSafe.foldl (fun s n => s.insert n) ∅
  let (_, s) ← StateT.run (s := ({ env, replayed := .start rfl, remaining } :
      State cfg.fuel (· = env))) do
    match decl with
    | some d => replayConstant hooks cfg d
    | none =>
      for n in remaining do
        replayConstant hooks cfg n
    checkPostponedConstructors cfg
    checkPostponedRecursors cfg
    if cfg.checkQuot then checkQuotInit cfg
  let checked := match decl with
    | none => allSafe
    | some _ => allSafe.filter fun n => !s.remaining.contains n
  let targetOk : Bool := match decl with
    | none => true
    | some d => checked.contains d && cfg.newConstants.contains d
  if ht : targetOk = false then
    throw (ReplayError.msg s!"target {decl.getD .anonymous} was not replayed")
  else
    match h : agreementError? cfg.newConstants s.env checked with
    | some e => throw e
    | none =>
      return {
        env := s.env
        numAdded := s.numAdded
        checked
        replayed := s.replayed
        agree := agreementError?_eq_none h
        complete := by
          rintro rfl n ci hci hu hp
          exact mem_safeNames hci hu hp
        target := by
          rintro d rfl
          simp only [targetOk, Bool.not_eq_false, Bool.and_eq_true, List.contains_iff_mem] at ht
          exact ⟨ht.1, _,
            Std.HashMap.getElem?_eq_some_getElem (Std.HashMap.mem_iff_contains.2 ht.2)⟩ }

/-- The pure replay core. -/
def replayPure (cfg : Config) (env : Environment) (decl : Option Name := none) :
    Except ReplayError (ReplayResult cfg env decl) :=
  replayCore Hooks.none cfg env decl

/-- The configuration of `--fresh` mode: the quotient check is skipped (the replay itself
initializes the quotient module when it reaches `Quot`). -/
def freshConfig (src : Std.HashMap Name ConstantInfo) (fuel : Lean4Lean.FuelConfig := {}) :
    Config :=
  { newConstants := src, checkQuot := false, fuel }

/-- The start environment of `--fresh` mode. `stage₁ := false` is very important here: while a
declaration is being added the environment is also held by the replay state, so the map is
shared and `stage₁ := true` would lead to quadratic performance. -/
def freshStart (mainModule : Name) : Environment :=
  Kernel.Environment.empty mainModule false

/-- The pure replay of `src` from the empty environment, as in `--fresh` mode. -/
def replayFresh (src : Std.HashMap Name ConstantInfo) (mainModule : Name := .anonymous)
    (fuel : Lean4Lean.FuelConfig := {}) (decl : Option Name := none) :
    Except ReplayError (ReplayResult (freshConfig src fuel) (freshStart mainModule) decl) :=
  replayPure (freshConfig src fuel) (freshStart mainModule) decl

/-! ### The IO wrapper -/

/-- Configuration of the IO driver: the core configuration and the logging options. -/
structure Context extends Config where
  verbose := false
  compare := false

/-- Use a fresh `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Exception) : IO α := do
  let options := pp.match.set (pp.rawOnError.set {} true) false
  -- Note: because the environment we are using has no extension state,
  -- we cannot safely use it with lean functions like the pretty printer.
  -- Here we instead create a fresh environment, which is good enough to get
  -- basic pretty printing working.
  let env ← mkEmptyEnvironment
  let ex ← ex.mapEnvM fun _ => return env.toKernelEnv
  Prod.fst <$> (Lean.Core.CoreM.toIO · { fileName := "", options, fileMap := default } { env }) do
    Lean.throwKernelException ex

/-- The `IO.Error` the driver reports for a `ReplayError`. -/
def ReplayError.toIOError : ReplayError → IO IO.Error
  | .kernel name ex => do
    let e ← try throwKernelException ex catch e => pure e
    return IO.userError s!"at {name}: {e.toString}"
  | .msg s => return IO.userError s

/-- The hooks of the executable: verbose logging, reporting of slow declarations, and the
optional comparison with the C++ kernel (`--compare`). -/
def ioHooks (ctx : Context) : Hooks (ExceptT ReplayError IO) where
  beforeAdd d := do
    if ctx.verbose then
      println! "adding {d.name}"
    IO.monoMsNow
  afterAdd name d env _ t1 := do
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      if ctx.compare then
        let t3 ← match env.addDecl {} d with
        | .ok _ => IO.monoMsNow
        | .error ex => throw (ReplayError.kernel name ex)
        if (t2 - t1) > 2 * (t3 - t2) then
          println!
            "{env.header.mainModule}:{d.name}: lean took {t3 - t2}, lean4lean took {t2 - t1}"
        else
          println! "{env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"
      else
        println! "{env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"

/-- "Replay" some constants into an `Environment`, sending them to the kernel for checking.
This runs the replay core `replayCore` with the IO hooks. -/
def replay (ctx : Context) (env : Environment) (decl : Option Name := none) :
    IO (Nat × Environment) := do
  match ← (replayCore (ioHooks ctx) ctx.toConfig env decl).run with
  | .ok r => return (r.numAdded, r.env)
  | .error e => throw (← e.toIOError)

/-! ### Differential replay against the C++ kernel (`--differential`)

With `--differential`, every declaration the replay sends to lean4lean is also sent to the C++
kernel (`Kernel.Environment.addDecl`, with no heartbeat limit), on the same environment: the one
lean4lean has built so far. The two answers are compared, and when both accept, the constants
the declaration adds (the declared names, and for an inductive block its constructors, its
recursors and the auxiliary recursors `rec_i` of a nested block) are compared under `==`, so the
terms lean4lean constructs (recursor types and rules, constructor types, the quotient
constants) are checked against the C++ kernel's. A lean4lean rejection stops the replay, as
without the flag; it is then classified by running the C++ kernel on the rejected declaration.
This does not change what lean4lean checks or the replay core; it only adds hooks. -/

/-- The counts of a differential replay. -/
structure DiffCounts where
  /-- Declarations sent to both kernels. -/
  checked := 0
  /-- Both accept, and every constant the declaration adds is `==` in the two environments. -/
  agreements := 0
  /-- lean4lean rejects, the C++ kernel accepts. -/
  lean4leanOnly := 0
  /-- lean4lean accepts, the C++ kernel rejects. -/
  kernelOnly := 0
  /-- Both reject. -/
  bothReject := 0
  /-- Both accept, but some constant the declaration adds differs between the two. -/
  termMismatches := 0
  deriving Inhabited

/-- The number of disagreements of a differential replay. -/
def DiffCounts.disagreements (c : DiffCounts) : Nat :=
  c.lean4leanOnly + c.kernelOnly + c.termMismatches

instance : ToString DiffCounts where
  toString c := s!"{c.checked} declarations checked, {c.agreements} agreements, \
    {c.lean4leanOnly} lean4lean-only rejections, {c.kernelOnly} kernel-only rejections, \
    {c.bothReject} rejected by both, {c.termMismatches} constructed-term mismatches"

/-- The state of a differential replay: the counts, and the environment and declaration of the
pending `addDecl`, to classify a lean4lean rejection. -/
structure DiffState where
  counts : DiffCounts := {}
  lastEnv : Environment
  lastDecl : Option Declaration := none

/-- The options of the C++ kernel in a differential replay: no heartbeat limit, so that a
declaration elaborated under a raised `maxHeartbeats` is not a spurious rejection. -/
def diffOptions : Options := Options.empty.set `maxHeartbeats (0 : Nat)

/-- The names of the constants a declaration adds, as far as both kernels are compared. For an
inductive block: the types, their constructors and recursors, and the auxiliary recursors
`rec_i` of a nested block (probed until absent from both environments). -/
def addedNames (d : Declaration) (env₁ env₂ : Environment) : List Name :=
  match d with
  | .axiomDecl v => [v.name]
  | .defnDecl v => [v.name]
  | .thmDecl v => [v.name]
  | .opaqueDecl v => [v.name]
  | .mutualDefnDecl vs => vs.map (·.name)
  | .quotDecl => [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  | .inductDecl _ _ ts _ =>
    let main := ts.flatMap fun t => t.name :: Name.str t.name "rec" :: t.ctors.map (·.name)
    let aux := match ts with
      | t :: _ => go t.name 1 1000
      | [] => []
    main ++ aux
where
  /-- `n.rec_i, n.rec_(i+1), …` while present in either environment. -/
  go (n : Name) (i : Nat) : Nat → List Name
    | 0 => []
    | fuel + 1 =>
      let r := Name.str n s!"rec_{i}"
      if (env₁.find? r).isSome || (env₂.find? r).isSome then r :: go n (i + 1) fuel else []

/-- The hooks of a differential replay: the IO hooks, and after each successful lean4lean
`addDecl`, the same declaration sent to the C++ kernel on the environment lean4lean started
from, with the added constants compared. -/
def diffHooks (ctx : Context) (ref : IO.Ref DiffState) : Hooks (ExceptT ReplayError IO) where
  beforeAdd d := do
    ref.modify fun s => { s with lastDecl := some d }
    (ioHooks ctx).beforeAdd d
  afterAdd name d env env' t := do
    (ioHooks ctx).afterAdd name d env env' t
    let counts ← match env.addDecl diffOptions d with
    | .error ex =>
      let e ← (ReplayError.kernel name ex).toIOError
      IO.eprintln s!"differential: kernel-only rejection of {d.name}: {e}"
      pure fun (c : DiffCounts) => { c with kernelOnly := c.kernelOnly + 1 }
    | .ok cenv =>
      let bad := (addedNames d env' cenv).filter fun n => !(env'.find? n == cenv.find? n)
      if bad.isEmpty then
        pure fun (c : DiffCounts) => { c with agreements := c.agreements + 1 }
      else
        IO.eprintln s!"differential: constructed-term mismatch in {d.name}: {bad}"
        pure fun (c : DiffCounts) => { c with termMismatches := c.termMismatches + 1 }
    ref.modify fun s =>
      { s with lastEnv := env', lastDecl := none,
               counts := counts { s.counts with checked := s.counts.checked + 1 } }

/-- `replay` with the differential hooks. A lean4lean rejection is classified by the C++ kernel
and then reported as by `replay`. Returns the counts with the result. -/
def replayDifferential (ctx : Context) (env : Environment) (decl : Option Name := none) :
    IO (DiffCounts × Nat × Environment) := do
  let ref ← IO.mkRef ({ lastEnv := env } : DiffState)
  match ← (replayCore (diffHooks ctx ref) ctx.toConfig env decl).run with
  | .ok r => return ((← ref.get).counts, r.numAdded, r.env)
  | .error e =>
    let s ← ref.get
    if let (.kernel _ _, some d) := (e, s.lastDecl) then
      let c := s.counts
      let c := match s.lastEnv.addDecl diffOptions d with
        | .ok _ =>
          { c with checked := c.checked + 1, lean4leanOnly := c.lean4leanOnly + 1 }
        | .error _ => { c with checked := c.checked + 1, bothReject := c.bothReject + 1 }
      if c.lean4leanOnly > s.counts.lean4leanOnly then
        IO.eprintln s!"differential: lean4lean-only rejection of {d.name}"
      IO.println s!"differential: {c}"
    throw (← e.toIOError)

/-- Print the counts of a differential replay of `module`, and fail on a disagreement. -/
def reportDifferential (module : Name) (c : DiffCounts) : IO Unit := do
  IO.println s!"differential {module}: {c}"
  if c.disagreements > 0 then
    throw <| IO.userError s!"differential replay of {module}: {c.disagreements} disagreements \
      with the C++ kernel"

open private ImportedModule.mk from Lean.Environment in
/-- Replay the constants of `module` into the environment of its imports. The imported
environment is trusted. -/
unsafe def replayFromImports (module : Name) (verbose := false) (compare := false)
    (fuel : Lean4Lean.FuelConfig := {}) (differential := false) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (mod, _) := parts[parts.size - 1]? | unreachable! -- load private module data
  let (_, s) ← (importModulesCore mod.imports).run
  let env ← match Kernel.Environment.finalizeImport s mod.imports module 0 with
    | .ok env => pure env
    | .error e => throw <| .userError <| ← (e.toMessageData {}).toString
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let ctx : Context := { newConstants, verbose, compare, fuel }
  let (counts?, n, env') ← if differential then
      (fun (c, r) => (some c, r)) <$> replayDifferential ctx env
    else (none, ·) <$> replay ctx env
  (Environment.ofKernelEnv env').freeRegions
  -- Project out the regions *before* freeing them: `CompactedRegion` is a `USize`, so the
  -- projected array holds no pointers into the regions, and `parts` -- whose `ModuleData`s
  -- live inside them -- is consumed by the `map` and dead by the time we free. Iterating
  -- `parts` directly would leave this frame's own locals dangling, and the decrefs on
  -- return would segfault.
  parts.map (·.2) |>.forM CompactedRegion.free
  if let some c := counts? then reportDifferential module c
  pure n

/-- Replay all the constants of `module` (imported and defined in it) into the empty
environment. This is `replayFresh` run with the IO hooks (the differential hooks, with
`differential`). -/
unsafe def replayFromFresh (module : Name)
    (verbose := false) (compare := false) (decl : Option Name := none)
    (fuel : Lean4Lean.FuelConfig := {}) (differential := false) : IO Nat := do
  Lean.withImportModules #[module] {} (trustLevel := 0) fun env => do
    let ctx := { freshConfig env.constants.map₁ fuel with verbose, compare }
    if differential then
      let (c, n, _) ← replayDifferential ctx (freshStart module) decl
      reportDifferential module c
      pure n
    else
      Prod.fst <$> replay ctx (freshStart module) decl

end Lean4Lean.Replay
