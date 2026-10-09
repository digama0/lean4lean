import Lean4Lean.Verify.Environment.Primitive.Clauses
import Lean4Lean.Verify.Environment.Primitive.DivMod
import Lean4Lean.Verify.Environment.Primitive.Gcd
import Lean4Lean.Verify.Environment.Primitive.Bitwise

/-! Verification of primitive declarations. -/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-! ### Conservation

The value reflects in the environment the checker ran in, where `HasPrimitives` is available.
`addDefEq` then makes the constant equal to the value, so the constant reflects in the
extension -- and every other spec transfers by monotonicity. Nothing is assumed about
`HasPrimitives` at the extension, which is what is being established. -/

/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer.

The recognizer's `isDefEq` calls are about `v.value` and `v.type`, so lifting them into the
model requires their translations. `addDefinition` establishes those before calling the
recognizer -- that is what the reordering there is for -- and they arrive here as `hvalue` and
`htype`, describing the very `ci'` that the caller goes on to add. -/
theorem checkDef.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal)
    (hu : v.levelParams.length = ci'.uvars)
    (htype : TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type)
    (hvalue : TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value)
    (hci : ci'.WF (ves.venv .safe))
    (state : State := {}) :
    (checkDef v).WF (.mk' wf .safe v.levelParams fuel) state fun allow _ =>
      allow → PrimitiveResult (ves.venv .safe) v ci' := by
  have P : Data v ci' (.mk' wf .safe v.levelParams fuel) := ⟨rfl, rfl, hu, htype, hvalue, hci⟩
  unfold checkDef; split
  · exact (checkNatAdd.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatPred.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatSub.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatMul.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatPow.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatMod.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatDiv.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatGcd.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatBEq.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatBLE.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatBitwise.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatLAnd.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatLOr.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatXor.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatShiftLeft.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkNatShiftRight.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkCharOfNat.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact (checkStringOfList.WF wf ‹_› P).bind fun _ _ _ h => .pure fun _ => h
  · exact .pure nofun

/-! ### The primitive inductives

`Bool` and `Nat` are not defined but declared, so the recognizer's inductive clause is a guard
rather than a check of equations: it is what stops a declaration from taking one of those two
names without the shape the model assumes for it. -/

/-- Adding a run of constants, one after another. Whatever `AddInduct` turns out to be, this is
the part of it the primitive invariant depends on: the declared type and its constructors become
constants of the types declared for them, and nothing else changes. -/
inductive AddsConsts : VEnv → List (Name × VExpr) → VEnv → Prop
  | id {env} : AddsConsts env [] env
  | const {env env₁ env₂ n ty l} : env.addConst n ⟨0, ty⟩ = some env₁ →
    AddsConsts env₁ l env₂ → AddsConsts env ((n, ty) :: l) env₂
  | defeq : AddsConsts (env.addDefEq df) l env₂ → AddsConsts env l env₂

/-- A constant already present survives the run: a later step cannot take its name, because
`addConst` at a name that is already there fails. -/
theorem AddsConsts.constants_stable {venv env' : VEnv} {cs} (H : AddsConsts venv cs env')
    {n ci} (h : venv.constants n = some ci) : env'.constants n = some ci := by
  induction H with
  | id => exact h
  | defeq hadd ih => exact ih h
  | @const env env₁ _ m ty l hadd _ ih =>
    refine ih ?_
    have hne : m ≠ n := by
      rintro rfl; unfold VEnv.addConst at hadd; rw [h] at hadd; exact absurd hadd nofun
    rw [VEnv.addConst_constants_eq hadd]; simp [hne, h]

/-- Each constant of the run is present at the end, with the type it was added at. -/
theorem AddsConsts.constants_of_mem {venv env' : VEnv} {cs} (H : AddsConsts venv cs env')
    {n ty} (hmem : (n, ty) ∈ cs) : env'.constants n = some ⟨0, ty⟩ := by
  induction H with
  | id => cases hmem
  | defeq hadd ih => exact ih hmem
  | @const env env₁ _ m ty' l hadd hrest ih =>
    obtain h | h := List.mem_cons.1 hmem
    · cases h; apply hrest.constants_stable; rw [VEnv.addConst_constants_eq hadd]; simp
    · exact ih h

/-- A spec whose name is none of the ones being added survives the run. -/
theorem AddsConsts.holds_of_ne {venv env' : VEnv} {cs} (H : AddsConsts venv cs env')
    {n : Name} {s : PrimSpec} (hs : s.Holds venv n) (hne : ∀ q ∈ cs, q.1 ≠ n) :
    s.Holds env' n := by
  induction H with
  | id => exact hs
  | defeq hadd ih => exact ih hs.addDefEq hne
  | @const env env₁ env₂ m ty l hadd _ ih =>
    exact ih (hs.addConst (hne _ (.head _)) hadd) fun q hq => hne q (.tail _ hq)

/-- The constants `Bool`'s declaration contributes. -/
def boolConsts : List (Name × VExpr) :=
  [(``Bool, vexpr(Type)), (``false, .bool), (``true, .bool)]

/-- The constants `Nat`'s declaration contributes. -/
def natConsts : List (Name × VExpr) :=
  [(``Nat, vexpr(Type)), (``Nat.zero, .nat), (``Nat.succ, .forallE .nat .nat)]

theorem AddsConsts.hasPrimitives_bool {venv env' : VEnv} (H : AddsConsts venv boolConsts env')
    (hprim : venv.HasPrimitives) : env'.HasPrimitives := by
  intro (p, s) hp
  by_cases hx : ∀ q ∈ boolConsts, q.fst ≠ p
  · exact H.holds_of_ne (hprim _ hp) hx
  simp at hx
  have ⟨x, hx⟩ := hx
  have := List.mem_map_of_mem (f := (·.1)) hx
  simp only [boolConsts, List.map, List.mem_cons, List.not_mem_nil, or_false] at this
  obtain rfl|rfl|rfl := this <;> simp [primSpecs] at hp <;> subst hp
  · rintro _ _ (_ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩)
    · exact ⟨_, H.constants_of_mem (.tail _ (.head _))⟩
    · exact ⟨_, H.constants_of_mem (.tail _ (.tail _ (.head _)))⟩
  · intro _ h; cases H.constants_of_mem (.tail _ (.head _)) |>.symm.trans h; rfl
  · intro _ h; cases H.constants_of_mem (.tail _ (.tail _ (.head _))) |>.symm.trans h; rfl

theorem AddsConsts.hasPrimitives_nat {venv env' : VEnv} (H : AddsConsts venv natConsts env')
    (hprim : venv.HasPrimitives) : env'.HasPrimitives := by
  intro (p, s) hp
  by_cases hx : ∀ q ∈ natConsts, q.fst ≠ p
  · exact H.holds_of_ne (hprim _ hp) hx
  simp at hx
  have ⟨x, hx⟩ := hx
  have := List.mem_map_of_mem (f := (·.1)) hx
  simp only [natConsts, List.map, List.mem_cons, List.not_mem_nil, or_false] at this
  obtain rfl|rfl|rfl := this <;> simp [primSpecs] at hp <;> subst hp
  · rintro _ _ (_ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩)
    · exact ⟨_, H.constants_of_mem (.tail _ (.head _))⟩
    · exact ⟨_, H.constants_of_mem (.tail _ (.tail _ (.head _)))⟩
  · intro _ h; cases H.constants_of_mem (.tail _ (.head _)) |>.symm.trans h; rfl
  · intro _ h; cases H.constants_of_mem (.tail _ (.tail _ (.head _))) |>.symm.trans h; rfl

/-- What the recognizer's flag is worth for an inductive declaration: it is one of the two
primitive inductives in its standard form -- safe, no level parameters, no parameters, a single
type at `Type`, and the constructors `primSpecs` speaks about -- and adding the constants it
contributes keeps the primitive invariant.

The second half is what the guard is *for*: `containsImplies` needs the constructors to arrive
with the type, and the two `typeEq` entries need them to have exactly the declared types. What is
still missing is the other side of the handshake -- a constructive `AddInduct` whose added
constants are these, which is what `addDecl.WF`'s `inductDecl` case waits on. -/
def PrimitiveInductiveResult (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  isUnsafe = false ∧ lparams = [] ∧ nparams = 0 ∧
  ∃ (type : InductiveType) (cs : List (Name × VExpr)),
    types = [type] ∧ type.type = q(Type) ∧
    (type.name = ``Bool ∧ cs = boolConsts ∧
      type.ctors = [⟨``false, q(Bool)⟩, ⟨``true, q(Bool)⟩] ∨
    type.name = ``Nat ∧ cs = natConsts ∧ ∃ nm bi,
      type.ctors = [⟨``Nat.zero, q(Nat)⟩, ⟨``Nat.succ, .forallE nm q(Nat) q(Nat) bi⟩]) ∧
    ∀ {venv env' : VEnv}, venv.HasPrimitives → AddsConsts venv cs env' → env'.HasPrimitives

/-- Verification boundary for the recognizer's inductive clause. -/
theorem checkInductive.WF (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) :
    (checkInductive env lparams nparams types isUnsafe).WF fun b =>
      b → PrimitiveInductiveResult lparams nparams types isUnsafe := by
  rintro b hrun rfl
  unfold checkInductive at hrun
  simp only [bind, Except.bind] at hrun
  split at hrun <;> [rename_i hguard; simp [pure, Except.pure] at hrun]
  obtain ⟨⟨hunsafe, hlparams⟩, hnparams⟩ :
      (isUnsafe = false ∧ lparams = []) ∧ nparams = 0 := by simpa using hguard
  subst isUnsafe; subst lparams; subst nparams
  split at hrun <;> [rename_i type; cases hrun]
  split at hrun <;> [rename_i htype; cases hrun]
  have htypeEq := Expr.eqv_sort.mp htype
  split at hrun
  · rename_i hname; split at hrun <;> [skip; cases hrun]
    exact ⟨rfl, rfl, rfl, type, boolConsts, rfl, htypeEq,
      .inl ⟨hname, rfl, ‹_›⟩, fun hprim H => H.hasPrimitives_bool hprim⟩
  · rename_i hname; split at hrun <;> [skip; cases hrun]
    exact ⟨rfl, rfl, rfl, type, natConsts, rfl, htypeEq,
      .inr ⟨hname, rfl, _, _, ‹_›⟩, fun hprim H => H.hasPrimitives_nat hprim⟩
  · cases hrun
