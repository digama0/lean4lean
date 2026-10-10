import Lean4Lean.Verify.Typing.TrTerm
import Lean4Lean.Verify.Typing.PrimSpec

/-!
# Reflection for the primitive definitions

`Primitive.checkDef` probes a definition's *value* on critical constructors and never inspects
its identity: the value stays an opaque `VExpr` throughout, and only the checked `isDefEq`
facts about it are used. This file turns those facts into the `Reflects*` statements that
`VEnv.HasPrimitives` records.

The equations arrive in *open* form, because the checker binds its probe variables with
`withLocalDecl` rather than building lambdas: for a binary `Nat` primitive the zero equation
lives in context `[.nat]` and the successor equation in `[.nat, .nat]`, with `.bvar 0` the
most recently bound variable.
-/

namespace Lean4Lean

open Lean

variable {env : VEnv}

/-! ### Typing of the constructors and numerals

`TrExprS.natZero`/`.natSucc`/`.natLit` already derive these from `HasPrimitives`; the wrappers
below just restate them at an arbitrary context, which is the form the recurrence proofs use. -/

theorem VEnv.HasPrimitives.natZeroT (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (Γ) :
    env.HasType 0 Γ .natZero .nat :=
  HasType.weak0 henv (TrExprS.natZero (Us := []) (Δ := []) hprim hnat).2

theorem VEnv.HasPrimitives.natSuccT (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (Γ) :
    env.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
  HasType.weak0 henv (TrExprS.natSucc (Us := []) (Δ := []) hprim hnat).2

theorem VEnv.HasPrimitives.natPredT (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hpred : env.contains ``Nat.pred) (Γ) :
    env.HasType 0 Γ (.const ``Nat.pred []) (.forallE .nat .nat) :=
  (hprim.natPred hpred).1.weak0 henv

/-- Anything typed as a function *from* `Nat` forces `Nat` to be present. Branches whose guard
names some other primitive -- `Nat.sub` guards on `Nat.pred`, `Nat.mul` on `Nat.add` -- get
`Nat` this way, from the typing clause of that primitive's reflection. -/
theorem VEnv.contains_nat_of_hasType (henv : env.OrderedStrong) {e A : VExpr}
    (h : env.HasType 0 [] e (.forallE .nat A)) : env.contains ``Nat := by
  obtain ⟨_, hT⟩ := (h.isType henv trivial).forallE_inv henv |>.1
  obtain ⟨_, hci, -, -⟩ := hT.const_inv henv trivial
  exact ⟨_, hci⟩

theorem VEnv.HasPrimitives.natOfPred (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hpred : env.contains ``Nat.pred) : env.contains ``Nat :=
  VEnv.contains_nat_of_hasType henv (hprim.natPred hpred).1

theorem VEnv.HasPrimitives.natOfAdd (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hadd : env.contains ``Nat.add) : env.contains ``Nat :=
  VEnv.contains_nat_of_hasType henv (hprim.natAdd hadd).1

theorem VEnv.HasPrimitives.natOfMul (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hmul : env.contains ``Nat.mul) : env.contains ``Nat :=
  VEnv.contains_nat_of_hasType henv (hprim.natMul hmul).1

theorem VEnv.HasPrimitives.natOfDiv (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hdiv : env.contains ``Nat.div) : env.contains ``Nat :=
  VEnv.contains_nat_of_hasType henv (hprim.natDiv hdiv).1

theorem VEnv.HasPrimitives.natOfMod (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hmod : env.contains ``Nat.mod) : env.contains ``Nat :=
  VEnv.contains_nat_of_hasType henv (hprim.natMod hmod).1

/-- `Nat.bitwise`'s recorded type is the only place `Bool` appears among the bitwise operations'
prerequisites, so this is how `Nat.land`/`Nat.lor`/`Nat.xor` -- which guard on `Nat.bitwise`
alone -- learn that `Bool` is present. -/
theorem VEnv.HasPrimitives.boolOfBitwise (henv : env.OrderedStrong) (hprim : env.HasPrimitives)
    (hbw : env.contains ``Nat.bitwise) : env.contains ``Bool := by
  obtain ⟨ci, hci⟩ := hbw
  cases (hprim.natBitwise ⟨ci, hci⟩).1 _ hci
  obtain ⟨_, hT⟩ := ((henv.ordered.constWF hci).forallE_inv henv).1.forallE_inv henv |>.1
  obtain ⟨_, hc, -, -⟩ := hT.const_inv henv trivial
  exact ⟨_, hc⟩

theorem VEnv.HasPrimitives.natLitT (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (k Γ) :
    env.HasType U Γ (.natLit k) .nat :=
  VExpr.instL_natLit ▸ (TrExprS.natLit (Us := []) (Δ := []) hprim hnat k).2.instL (ls := []) nofun
    |>.weak0 henv

theorem VExpr.closedN_natLit : (VExpr.natLit n).ClosedN k := by
  induction n <;> simp [VExpr.natLit, VExpr.natZero, VExpr.natSucc, ClosedN, *]

/-- The measure lambda a caller hands to `unfoldNatWellFounded` -- `fun m _ : Nat => m` -- at
ground arguments. Two beta steps; the literals are closed, so neither the lift under the inner
binder nor the final instantiation disturbs them. -/
theorem VEnv.HasPrimitives.natFstLamApp (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (x y : Nat) :
    env.IsDefEqU U Γ
      (((VExpr.lam .nat (.lam .nat (.bvar 1))).app (.natLit x)).app (.natLit y)) (.natLit x) := by
  have hlit {Γ'} k : env.HasType U Γ' (.natLit k) .nat := hprim.natLitT henv hnat k Γ'
  have hNat {Γ'} (h : OnCtx Γ' (env.IsType U)) : env.IsType U Γ' .nat := (hlit 0).isType henv h
  obtain ⟨_, hu⟩ := hNat (Γ' := VExpr.nat :: Γ) ⟨hΓ, hNat hΓ⟩
  -- `(fun m _ => m) x` steps to `fun _ => x`, the lift over the discarded binder being trivial
  have step1 : env.IsDefEq U Γ (.app (.lam .nat (.lam .nat (.bvar 1))) (.natLit x))
      (.lam .nat (.natLit x)) (.forallE .nat .nat) := by
    have := VEnv.IsDefEq.beta (e := .lam .nat (.bvar 1)) (e' := .natLit x)
      (.lamDF hu (.bvar (.succ .zero))) (hlit x)
    simpa [VExpr.inst, VExpr.instVar,
      VExpr.closedN_natLit.liftN_eq (Nat.zero_le _)] using this
  refine ⟨_, .trans (.appDF step1 (hlit y)) ?_⟩
  simpa using VEnv.IsDefEq.beta (e := .natLit x) (e' := .natLit y) (hlit x) (hlit y)

theorem VEnv.HasPrimitives.natIsType (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Us : List Name} {Δ : VLCtx}
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    env.IsType Us.length Δ.toCtx .nat :=
  (TrExprS.natZero (Us := Us) (Δ := Δ) hprim hnat).2.isType henv hΔ

/-- `Nat` translates to `.nat`. The `uvars = 0` side condition comes from `Nat.zero`'s recorded
type being `.nat`: that type is well formed, and `const_inv` reads the arity off it. -/
theorem VEnv.HasPrimitives.trNat (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Us : List Name} {Δ : VLCtx} :
    TrExprS env Us Δ (.const ``Nat []) .nat := by
  obtain ⟨_, hT⟩ := hprim.natIsType (Us := []) (Δ := []) henv hnat trivial
  obtain ⟨ci, hci, -, hlen⟩ := hT.const_inv henv trivial
  exact .const hci rfl hlen

theorem VEnv.HasPrimitives.boolLitT (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) (b Γ) :
    env.HasType 0 Γ (.boolLit b) .bool :=
  HasType.weak0 henv (TrExprS.boolLit (Us := []) (Δ := []) hprim hbool b).2

theorem VEnv.HasPrimitives.boolIsType (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) {Us : List Name} {Δ : VLCtx}
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    env.IsType Us.length Δ.toCtx .bool :=
  (TrExprS.boolLit (Us := Us) (Δ := Δ) hprim hbool true).2.isType henv hΔ

theorem VEnv.HasPrimitives.trBool (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) {Us : List Name} {Δ : VLCtx} :
    TrExprS env Us Δ (.const ``Bool []) .bool := by
  obtain ⟨_, hT⟩ := hprim.boolIsType (Us := []) (Δ := []) henv hbool trivial
  obtain ⟨_, hci, -, hlen⟩ := hT.const_inv henv trivial
  exact .const hci rfl hlen

/-- The translation of a checked unary `Nat` arrow type; `Nat.pred` is the only primitive with
this shape. -/
theorem TrExprS.natArrow1 {env : VEnv} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Us : List Name}
    {n₁ : Name} {d₁ : MData} {bi₁ : BinderInfo} {codSrc : Expr}
    (hcod : TrTy env Us [(none, .vlam .nat)] codSrc) :
    TrExprS env Us [] (.forallE n₁ (.mdata d₁ (.const ``Nat [])) codSrc bi₁)
      (.forallE .nat hcod.tgt) :=
  (TrTy.forallE (.mdata (.of (hprim.trNat henv hnat)
    (hprim.natIsType henv hnat (Δ := []) trivial))) hcod).trS

/-- A constant with no universe arguments translates to itself, and does so at any context --
which is how a translation obtained at the top level is reused under the arrow's binder. -/
theorem TrExprS.const0_inv {env : VEnv} {Us Us' : List Name} {Δ Δ' : VLCtx} {c : Name} {T : VExpr}
    (h : TrExprS env Us Δ (.const c []) T) :
    T = .const c [] ∧ TrExprS env Us' Δ' (.const c []) (.const c []) := by
  let .const hci hus hlen := h
  simp at hus; subst hus
  exact ⟨rfl, .const hci rfl hlen⟩

/-- The `String.ofList` branch works entirely with `List`-at-`Char` applications -- `List Char`,
`List.nil`, `List.cons` -- and each translates to the corresponding `VExpr` abbreviation. -/
theorem TrExprS.appChar_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {c : Name} {T : VExpr}
    (h : TrExprS env Us Δ (.app (.const c [.zero]) (.const ``Char [])) T) :
    T = .app (.const c [.zero]) .char := by
  let .app _ _ (.const _ hus _) ha := h; let .const _ hus2 _ := ha
  simp [VLevel.ofLevel] at hus hus2; subst hus; subst hus2; rfl

/-- The same, plus the translation rebuilt at any context: both parts of the application are
closed, so their typings weaken from the empty context to whatever the arrow builds. -/
theorem TrExprS.appChar_inv' {env : VEnv} {Us : List Name} {Δ' : VLCtx} {c : Name} {T : VExpr}
    (henv : env.OrderedStrong)
    (h : TrExprS env Us [] (.app (.const c [.zero]) (.const ``Char [])) T) :
    T = .app (.const c [.zero]) .char ∧
    TrExprS env Us Δ' (.app (.const c [.zero]) (.const ``Char []))
      (.app (.const c [.zero]) .char) ∧
    TrExprS env Us Δ' (.const ``Char []) .char := by
  let .app hfT haT (.const hci hus hlen) ha := h; let .const hci2 hus2 hlen2 := ha
  simp [VLevel.ofLevel] at hus hus2; subst hus; subst hus2
  refine ⟨rfl, ?_, .const hci2 rfl hlen2⟩
  exact .app (hfT.weak0 henv) (haT.weak0 henv) (.const hci rfl hlen) (.const hci2 rfl hlen2)

/-- `String.ofList`'s checked type, pinned the same way the `Nat` arrows are. -/
theorem TrExprS.listCharStringArrow_inv {env : VEnv} {Us : List Name}
    {n : Name} {bi : BinderInfo} {T : VExpr}
    (h : TrExprS env Us [] (.forallE n (.app (.const ``List [.zero]) (.const ``Char []))
      (.const ``String []) bi) T) :
    T = .forallE .listChar .string := by
  let .forallE _ _ hd hc := h
  cases hd.appChar_inv; cases (hc.const0_inv (Us' := Us) (Δ' := [])).1; rfl

/-- The checked type's translation already contains `Nat`. The bitwise operations guard on
`Nat.bitwise`, whose spec records no typing, so this is how they get `Nat`. -/
theorem TrExprS.contains_nat_of_natArrow2
    (h : TrExprS env Us [] (.forallE n₁ (.mdata d₁ (.const ``Nat []))
      (.forallE n₂ (.mdata d₂ (.const ``Nat [])) cod bi₂) bi₁) T) :
    env.contains ``Nat :=
  let .forallE _ _ (.mdata hd) _ := h; let .const hci _ _ := hd; ⟨_, hci⟩

/-- `Nat.land`/`Nat.lor`/`Nat.xor` match their value against `Nat.bitwise` applied to an
operator, and then probe that operator. Nothing checks the operator's type, so it has to be read
off `Nat.bitwise`'s recorded type through the application: unique typing gives the two function
types as definitionally equal, and `forallE` injectivity takes the domains apart. -/
theorem TrExprS.bitwiseOperand {env : VEnv} {Us : List Name} {opSrc : Expr} {V : VExpr}
    (henv : env.WF) (hprim : env.HasPrimitives)
    (h : TrExprS env Us [] (.app (.const ``Nat.bitwise []) opSrc) V) :
    ∃ op, V = .app (.const ``Nat.bitwise []) op ∧
      TrExprS env Us [] opSrc op ∧ env.HasType Us.length [] op .boolOp2 := by
  let .app hfT haT hf ha := h; let .const hci hus hlen := hf
  simp at hus; subst hus
  refine ⟨_, rfl, ha, ?_⟩
  cases (hprim.natBitwise ⟨_, hci⟩).1 _ hci
  have hT2 : env.HasType Us.length [] vexpr(Nat.bitwise) (.forallE .boolOp2 .natOp2) :=
    .const' hci (by simp) hlen <| by
      simp [VExpr.instL, VExpr.boolOp2, VExpr.natOp2, VExpr.bool, VExpr.nat]
  obtain ⟨⟨_, hdom⟩, -⟩ := (hfT.uniqU henv trivial hT2).forallE_inv henv trivial
  exact hdom.defeq haT

/-- The translation of a checked binary `Nat` arrow type, generic in the binder names and in the
annotations the compiler attaches -- which is what lets it serve `@& Nat → @& Nat → Nat` as the
prelude actually declares it. Combined with `TrExprS.eqv` and `TrExprS.unique` this pins a
primitive's `ci'.type` in one step. -/
theorem TrExprS.natArrow2 (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hcod : TrTy env Us [(none, .vlam .nat), (none, .vlam .nat)] codSrc) :
    TrExprS env Us [] (.forallE n₁ (.mdata d₁ (.const ``Nat []))
        (.forallE n₂ (.mdata d₂ (.const ``Nat [])) codSrc bi₂) bi₁)
      (.forallE .nat (.forallE .nat hcod.tgt)) := by
  have hOn0 : OnCtx (VLCtx.toCtx []) (env.IsType Us.length) := trivial
  have hN0 := hprim.natIsType henv hnat hOn0
  have hOn1 : OnCtx (VLCtx.toCtx [(none, .vlam .nat)]) (env.IsType Us.length) := ⟨hOn0, hN0⟩
  have hN1 := hprim.natIsType henv hnat hOn1
  exact (TrTy.forallE (.mdata (.of (hprim.trNat henv hnat) hN0))
    (.forallE (.mdata (.of (hprim.trNat henv hnat) hN1)) hcod)).trS

/-- Congruence for `IsDefEqU` under an application, with the typing supplied explicitly.
`IsDefEqU` hides the type, so the caller has to say at which type the two sides agree. -/
theorem VEnv.IsDefEqU.appDF' (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f f') (ha : env.IsDefEqU U Γ a a')
    (hfT : env.HasType U Γ f (.forallE A B)) (haT : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app f' a') :=
  ⟨_, .appDF (hf.of_l henv hΓ hfT) (ha.of_l henv hΓ haT)⟩

/-- The same, when only the argument moves. -/
theorem VEnv.IsDefEqU.app_arg' (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.IsDefEqU U Γ a a')
    (hfT : env.HasType U Γ f (.forallE A B)) (haT : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app f a') := .appDF' henv hΓ ⟨_, hfT⟩ ha hfT haT

/-- The same, when only the function moves. -/
theorem VEnv.IsDefEqU.app_fun' (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f f')
    (hfT : env.HasType U Γ f (.forallE A B)) (haT : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app f' a) := .appDF' henv hΓ hf ⟨_, haT⟩ hfT haT

/-- Recurrence for a binary `Nat` primitive whose successor equation applies a unary operation
`u` to the recursive call: `Nat.add` through `Nat.succ`, `Nat.sub` through `Nat.pred`.

This is about the definition's *value*, in the environment the checker ran in, and mentions no
constant at all -- `f` is an opaque `VExpr` and the proof uses only its typing and the two
probed equations. The constant acquires the reflection afterwards, in the extended environment,
through `congr_head`.

The probes are produced in a context whose level-parameter count is `v.levelParams.length`,
which is only *propositionally* zero -- the guard says `v.levelParams = []`. Taking `U` with
`hU : U = 0` lets the caller hand over its facts as they come, instead of rewriting them first. -/
theorem VEnv.ReflectsNatNatNat'.of_unary_step_equations (hU : U = 0)
    (henv : VEnv.WF env) (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (G : Nat → Nat)
    (huT : env.HasType 0 [] g (.forallE .nat .nat))
    (huClosed : g.ClosedN)
    (huEval : ∀ k, env.IsDefEqU 0 [] (.app g (.natLit k)) (.natLit (G k)))
    (hF0 : ∀ a, F a 0 = a)
    (hFs : ∀ a b, F a (b + 1) = G (F a b))
    (hfT : env.HasType U [] f (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU U [.nat] (.app (.app f (.bvar 0)) .natZero) (.bvar 0))
    (hs : env.IsDefEqU U [.nat, .nat]
      (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.app g (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat' f F := by
  subst hU; refine ⟨hfT, ?_⟩
  have hzeroT := hprim.natZeroT henv.orderedStrong hnat
  have hlit := hprim.natLitT henv.orderedStrong hnat (U := 0)
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hfClosed : f.ClosedN := (hfT.closedN' henv.ordered.closed trivial).1
  intro a b
  induction b with
  | zero =>
    rw [hF0]
    have := hz.instN henv.ordered .zero (hlit a [])
    simpa [VExpr.inst, hfClosed.instN_eq, VExpr.natLit] using this
  | succ b ih =>
    rw [hFs]
    -- instantiate the successor equation at `b` (innermost) and then at `a`
    have hb := hs.instN henv.ordered .zero (hlit b [.nat])
    have hab := hb.instN henv.ordered .zero (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq, huClosed.instN_eq] at hab
    refine hab.trans henv trivial <| .trans henv trivial ?_ (huEval (F a b))
    exact .app_arg' henv trivial ih huT (.app (.app hfT (hlit a [])) (hlit b []))

/-- Recurrence for a binary `Nat` primitive whose successor equation applies a *binary* operation
to the recursive call and the first argument, over a constant base: `Nat.mul` through `Nat.add`
with base `0`, `Nat.pow` through `Nat.mul` with base `1`.

Same shape as `of_unary_step_equations` otherwise -- `f` stays opaque, and the operator enters
only through its reflection, whose typing clause is what makes the congruence step available. -/
theorem VEnv.ReflectsNatNatNat'.of_binary_step_equations (hU : U = 0)
    (henv : VEnv.WF env) (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    (G : Nat → Nat → Nat) (Z E : Nat → Nat)
    (hg : env.ReflectsNatNatNat' g G)
    (hzE : ∀ a, z.inst (.natLit a) = .natLit (Z a))
    (heE : ∀ a b, (e.inst (.natLit b)).inst (.natLit a) = .natLit (E a))
    (hF0 : ∀ a, F a 0 = Z a)
    (hFs : ∀ a b, F a (b + 1) = G (F a b) (E a))
    (hfT : env.HasType U [] f (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU U [.nat]
      (.app (.app f (.bvar 0)) .natZero) z)
    (hs : env.IsDefEqU U [.nat, .nat]
      (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.app (.app g (.app (.app f (.bvar 1)) (.bvar 0))) e)) :
    env.ReflectsNatNatNat' f F := by
  subst hU; refine ⟨hfT, ?_⟩
  have hlit := hprim.natLitT henv.orderedStrong hnat (U := 0)
  have hfClosed : f.ClosedN := (hfT.closedN' henv.ordered.closed trivial).1
  have hgClosed : g.ClosedN := (hg.1.closedN' henv.ordered.closed trivial).1
  intro a b
  induction b with
  | zero =>
    rw [hF0]
    have := hz.instN henv.ordered .zero (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq, hzE a] at this
    exact this
  | succ b ih =>
    rw [hFs]
    have hb := hs.instN henv.ordered .zero (hlit b [.nat])
    have hab := hb.instN henv.ordered .zero (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq, hgClosed.instN_eq, heE a b] at hab
    have hfab := (hfT.app (hlit a [])).app (hlit b [])
    refine hab.trans henv trivial <| .trans henv trivial ?_ (hg.2 (F a b) (E a))
    exact .app_fun' henv trivial (.app_arg' henv trivial ih hg.1 hfab) (.app hg.1 hfab) (hlit _ [])

/-- Recurrence for a binary `Nat` primitive whose successor equation recurses with a *changed
first argument* rather than applying an operator to the result: `Nat.shiftLeft`, where
`shl x (succ y) ≡ shl (2 * x) y`. The induction therefore generalizes the first argument. -/
theorem VEnv.ReflectsNatNatNat'.of_first_arg_step_equations (hU : U = 0)
    (henv : VEnv.WF env) (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    (G : Nat → Nat → Nat) (C : Nat) (hg : env.ReflectsNatNatNat' g G)
    (hF0 : ∀ a, F a 0 = a)
    (hFs : ∀ a b, F a (b + 1) = F (G C a) b)
    (hfT : env.HasType U [] f (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU U [.nat]
      (.app (.app f (.bvar 0)) .natZero) (.bvar 0))
    (hs : env.IsDefEqU U [.nat, .nat]
      (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.app (.app f (.app (.app g (.natLit C)) (.bvar 1))) (.bvar 0))) :
    env.ReflectsNatNatNat' f F := by
  subst hU; refine ⟨hfT, ?_⟩
  have hlit := hprim.natLitT henv.orderedStrong hnat (U := 0)
  have hfClosed : f.ClosedN := (hfT.closedN' henv.ordered.closed trivial).1
  have hgClosed : g.ClosedN := (hg.1.closedN' henv.ordered.closed trivial).1
  intro a b
  induction b generalizing a with
  | zero =>
    rw [hF0]
    have := hz.instN henv.ordered .zero (hlit a [])
    simpa [VExpr.inst, hfClosed.instN_eq, VExpr.natLit] using this
  | succ b ih =>
    rw [hFs]
    have hb := hs.instN henv.ordered .zero (hlit b [.nat])
    have hab := hb.instN henv.ordered .zero (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq, hgClosed.instN_eq] at hab
    have hXT := (hg.1.app (hlit C [])).app (hlit a [])
    refine hab.trans henv trivial <| .trans henv trivial ?_ (ih (G C a))
    refine .app_fun' henv trivial ?_ (.app hfT hXT) (hlit b [])
    exact .app_arg' henv trivial (hg.2 C a) hfT hXT

/-- Recurrence for a binary `Nat` predicate given by its behaviour on the four constructor
combinations, the diagonal one recursing: `Nat.beq` and `Nat.ble`, which differ only in the
three constant answers. Both arguments are analysed, so this is a double induction rather than
a recursion on the second argument alone. -/
theorem VEnv.ReflectsNatNatBool'.of_constructor_cases (hU : U = 0) (henv : VEnv.WF env)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (b00 b0s bs0 : Bool)
    (hF00 : F 0 0 = b00) (hF0s : ∀ b, F 0 (b + 1) = b0s) (hFs0 : ∀ a, F (a + 1) 0 = bs0)
    (hFss : ∀ a b, F (a + 1) (b + 1) = F a b)
    (hfT : env.HasType U [] f (.forallE .nat <| .forallE .nat .bool))
    (h00 : env.IsDefEqU U [] (.app (.app f .natZero) .natZero) (.boolLit b00))
    (h0s : env.IsDefEqU U [.nat]
      (.app (.app f .natZero) (.app .natSucc (.bvar 0))) (.boolLit b0s))
    (hs0 : env.IsDefEqU U [.nat]
      (.app (.app f (.app .natSucc (.bvar 0))) .natZero) (.boolLit bs0))
    (hss : env.IsDefEqU U [.nat, .nat]
      (.app (.app f (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
      (.app (.app f (.bvar 1)) (.bvar 0))) :
    env.ReflectsNatNatBool' f F := by
  subst hU; refine ⟨hfT, ?_⟩
  have hlit := hprim.natLitT henv.orderedStrong hnat (U := 0)
  have hfClosed : f.ClosedN := (hfT.closedN' henv.ordered.closed trivial).1
  intro a b
  induction a generalizing b with
  | zero =>
    match b with
    | 0 => rw [hF00]; simpa [VExpr.natLit] using h00
    | k+1 =>
      rw [hF0s]
      have := h0s.instN henv.ordered .zero (hlit k [])
      simpa [VExpr.inst, hfClosed.instN_eq, VExpr.natLit] using this
  | succ a ih =>
    match b with
    | 0 =>
      rw [hFs0]
      have := hs0.instN henv.ordered .zero (hlit a [])
      simpa [VExpr.inst, hfClosed.instN_eq, VExpr.natLit] using this
    | k+1 =>
      rw [hFss]
      have hb := hss.instN henv.ordered .zero (hlit k [.nat])
      have hab := hb.instN henv.ordered .zero (hlit a [])
      simp [VExpr.inst, hfClosed.instN_eq] at hab
      exact hab.trans henv trivial (ih k)

/-- `Nat.land`/`Nat.lor` probe their `Bool` operator with the first argument a literal and the
second a bound variable, so instantiating each equation at a literal gives the reflection. The
two right-hand sides are described by `he₀`/`he₁`, which cover both a constant answer and the
variable itself. -/
theorem VEnv.ReflectsBoolBoolBool'.of_left_cases (hU : U = 0) (henv : VEnv.WF env)
    (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) (hfC : f.ClosedN)
    (hfT : env.HasType U [] f .boolOp2)
    (h0 : env.IsDefEqU U [.bool] (.app (.app f .boolFalse) (.bvar 0)) e₀)
    (h1 : env.IsDefEqU U [.bool] (.app (.app f .boolTrue) (.bvar 0)) e₁)
    (he₀ : ∀ b, e₀.inst (.boolLit b) = .boolLit (G false b))
    (he₁ : ∀ b, e₁.inst (.boolLit b) = .boolLit (G true b)) :
    env.ReflectsBoolBoolBool' f G := by
  have hlit := hprim.boolLitT henv.orderedStrong hbool
  subst hU; refine ⟨hfT, fun a b => ?_⟩
  match a with
  | false =>
    have := h0.instN henv.ordered .zero (hlit b [])
    simp [VExpr.inst, hfC.instN_eq, he₀ b] at this
    exact this
  | true =>
    have := h1.instN henv.ordered .zero (hlit b [])
    simp [VExpr.inst, hfC.instN_eq, he₁ b] at this
    exact this

/-- `Nat.xor` probes all four combinations with no binder at all. -/
theorem VEnv.ReflectsBoolBoolBool'.of_closed_cases {U : Nat} (hU : U = 0)
    {G : Bool → Bool → Bool} {f : VExpr} (hfT : env.HasType U [] f .boolOp2)
    (h : ∀ a b, env.IsDefEqU U [] (.app (.app f (.boolLit a)) (.boolLit b)) (.boolLit (G a b))) :
    env.ReflectsBoolBoolBool' f G := by subst hU; exact ⟨hfT, h⟩

/-- `Nat.pred`'s two probed equations reflect `Nat.pred`, for the value. Unlike the binary
primitives there is no recursion to unwind: the two cases of the literal *are* the two probes,
with the successor one instantiated at the numeral. -/
theorem VEnv.ReflectsNatNat'.of_pred_equations (hU : U = 0) (henv : VEnv.WF env)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {f : VExpr}
    (hfT : env.HasType U [] f (.forallE .nat .nat))
    (hz : env.IsDefEqU U [] (.app f .natZero) .natZero)
    (hs : env.IsDefEqU U [.nat] (.app f (.app .natSucc (.bvar 0))) (.bvar 0)) :
    env.ReflectsNatNat' f Nat.pred := by
  subst hU; refine ⟨hfT, fun a => ?_⟩
  have hfClosed : f.ClosedN := (hfT.closedN' henv.ordered.closed trivial).1
  match a with
  | 0 => exact hz
  | k+1 =>
    have := hs.instN henv.ordered .zero (hprim.natLitT henv.orderedStrong hnat k [])
    simpa [VExpr.inst, hfClosed.instN_eq, VExpr.natLit] using this

/-- Reflection transfers along a definitional equation on the head. In the environment
`addDefEq` produces, the constant is equal to the value, so it inherits the value's reflection
-- and this is the only place a constant enters. -/
theorem VEnv.ReflectsNatNatNat'.congr_head (henv : VEnv.WF env)
    (hlit : ∀ k Γ, env.HasType 0 Γ (.natLit k) .nat)
    (h : env.ReflectsNatNatNat' f F)
    (hgf : env.IsDefEqU 0 [] g f)
    (hgT : env.HasType 0 [] g (.forallE .nat <| .forallE .nat .nat)) :
    env.ReflectsNatNatNat' g F := by
  refine ⟨hgT, fun a b => ?_⟩
  refine VEnv.IsDefEqU.trans henv trivial ?_ (h.2 a b)
  have h₁ : env.IsDefEqU 0 [] (.app g (.natLit a)) (.app f (.natLit a)) :=
    .app_fun' henv trivial hgf hgT (hlit a [])
  exact .app_fun' henv trivial h₁ (.app hgT (hlit a [])) (hlit b [])

theorem VEnv.ReflectsNatNatBool'.congr_head (henv : VEnv.WF env)
    (hlit : ∀ k Γ, env.HasType 0 Γ (.natLit k) .nat)
    (h : env.ReflectsNatNatBool' f F)
    (hgf : env.IsDefEqU 0 [] g f)
    (hgT : env.HasType 0 [] g (.forallE .nat <| .forallE .nat .bool)) :
    env.ReflectsNatNatBool' g F := by
  refine ⟨hgT, fun a b => ?_⟩
  refine VEnv.IsDefEqU.trans henv trivial ?_ (h.2 a b)
  refine .app_fun' henv trivial ?_ (.app hgT (hlit a [])) (hlit b [])
  exact .app_fun' henv trivial hgf hgT (hlit a [])

theorem VEnv.ReflectsNatNat'.congr_head (henv : VEnv.WF env)
    (hlit : ∀ k Γ, env.HasType 0 Γ (.natLit k) .nat) {f g : VExpr} {F : Nat → Nat}
    (h : env.ReflectsNatNat' f F)
    (hgf : env.IsDefEqU 0 [] g f)
    (hgT : env.HasType 0 [] g (.forallE .nat .nat)) :
    env.ReflectsNatNat' g F :=
  ⟨hgT, fun a => .trans henv trivial (.app_fun' henv trivial hgf hgT (hlit a [])) (h.2 a)⟩

/-! ### Conservation

The value reflects in the environment the checker ran in, where `HasPrimitives` is available.
`addDefEq` then makes the constant equal to the value, so the constant reflects in the
extension -- and every other spec transfers by monotonicity. Nothing is assumed about
`HasPrimitives` at the extension, which is what is being established. -/

/-- The definitional equation `addDefEq` records for a `uvars = 0` definition. -/
theorem VEnv.isDefEqU_toDefEq {ci' : VDefVal}
    (hu : ci'.uvars = 0) (hwf : ci'.toDefEq.WF (env.addDefEq ci'.toDefEq)) :
    (env.addDefEq ci'.toDefEq).IsDefEqU 0 [] (.const ci'.name []) ci'.value := by
  have h := VEnv.IsDefEq.extra0 (env := env.addDefEq ci'.toDefEq) (.inl rfl) hwf
  refine ⟨ci'.type, ?_⟩
  simpa [VDefVal.toDefEq, hu, VLevel.params] using h

theorem VEnv.ReflectsNatNatNat'.mono
    (le : env ≤ env') (h : env.ReflectsNatNatNat' e F) : env'.ReflectsNatNatNat' e F :=
  ⟨h.1.mono le, fun a b => (h.2 a b).mono le⟩

theorem VEnv.ReflectsNatNatBool'.mono
    (le : env ≤ env') (h : env.ReflectsNatNatBool' e F) : env'.ReflectsNatNatBool' e F :=
  ⟨h.1.mono le, fun a b => (h.2 a b).mono le⟩

theorem VEnv.ReflectsNatNat'.mono
    (le : env ≤ env') (h : env.ReflectsNatNat' e F) : env'.ReflectsNatNat' e F :=
  ⟨h.1.mono le, fun a => (h.2 a).mono le⟩

/-- What both `toConst` transfers need from the extension: it is well formed, and the constant
is equal to the value there. Both facts are the `.def` step of `VDecl.WF`, so neither has to be
supplied by the caller. -/
theorem VDefVal.addDefEq_wf {ci' : VDefVal} (hwf : venv.WF)
    (hu : ci'.uvars = 0) (hci : ci'.WF venv)
    (hadd : venv.addConst ci'.name ci'.toVConstant = some env') :
    (env'.addDefEq ci'.toDefEq).WF ∧
      (env'.addDefEq ci'.toDefEq).IsDefEqU 0 [] (.const ci'.name []) ci'.value := by
  refine ⟨let ⟨_, h⟩ := hwf; ⟨_, .decl (.def hci hadd) h⟩, ?_⟩
  refine VEnv.isDefEqU_toDefEq hu ⟨?_, hci.mono <| (VEnv.addConst_le hadd).trans VEnv.addDefEq_le⟩
  simp only [VDefVal.toDefEq]
  rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
  have hc : env'.constants ci'.name = some ci'.toVConstant := VEnv.addConst_self hadd
  exact .const hc VLevel.id_WF (by simp)

/-- Carry a reflection of the definition's *value*, established in the environment the checker
ran in, onto the constant in the extension. Three steps in one: `≤` transports the reflection,
`addDefEq` makes the constant equal to the value there, and `congr_head` moves the reflection
across that equation.

The extension's well-formedness and the equation itself are both the `.def` step of `VDecl.WF`,
so neither has to be supplied by the caller. -/
theorem VEnv.ReflectsNatNatNat'.toConst {ci' : VDefVal}
    (hle : checked ≤ venv) (henv : checked.WF)
    (hwf : venv.WF) (hprim : checked.HasPrimitives) (hnat : checked.contains ``Nat)
    (hu : ci'.uvars = 0) (hci : ci'.WF venv)
    (hadd : venv.addConst ci'.name ci'.toVConstant = some env')
    (href : checked.ReflectsNatNatNat' ci'.value F) :
    (env'.addDefEq ci'.toDefEq).ReflectsNatNatNat' (.const ci'.name []) F := by
  have le : venv ≤ env'.addDefEq ci'.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have ⟨hwfE, hcf⟩ := VDefVal.addDefEq_wf hwf hu hci hadd
  replace href := href.mono (hle.trans le)
  exact VEnv.ReflectsNatNatNat'.congr_head hwfE
    (fun k Γ => (hprim.natLitT henv.orderedStrong hnat k Γ).mono (hle.trans le)) href hcf
    (HasType.defeqU_l hwfE trivial hcf.symm href.1)

theorem VEnv.ReflectsNatNatBool'.toConst {ci' : VDefVal}
    (hle : checked ≤ venv) (henv : checked.WF)
    (hwf : venv.WF) (hprim : checked.HasPrimitives) (hnat : checked.contains ``Nat)
    (hu : ci'.uvars = 0) (hci : ci'.WF venv)
    (hadd : venv.addConst ci'.name ci'.toVConstant = some env')
    (href : checked.ReflectsNatNatBool' ci'.value F) :
    (env'.addDefEq ci'.toDefEq).ReflectsNatNatBool' (.const ci'.name []) F := by
  have le : venv ≤ env'.addDefEq ci'.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have ⟨hwfE, hcf⟩ := VDefVal.addDefEq_wf hwf hu hci hadd
  replace href := href.mono (hle.trans le)
  refine congr_head hwfE (fun k Γ => ?_) href hcf (href.1.defeqU_l hwfE trivial hcf.symm)
  exact (hprim.natLitT henv.orderedStrong hnat k Γ).mono (hle.trans le)

/-- The unary counterpart. The reflection now carries a typing clause, and the constant's is
exactly what `congr_head` already needs, so it comes along for free. -/
theorem VEnv.ReflectsNatNat'.toConst {ci' : VDefVal}
    (hle : checked ≤ venv) (henv : checked.WF)
    (hwf : venv.WF) (hprim : checked.HasPrimitives) (hnat : checked.contains ``Nat)
    (hu : ci'.uvars = 0) (hci : ci'.WF venv)
    (hadd : venv.addConst ci'.name ci'.toVConstant = some env')
    (href : checked.ReflectsNatNat' ci'.value F) :
    (env'.addDefEq ci'.toDefEq).ReflectsNatNat' (.const ci'.name []) F := by
  have le : venv ≤ env'.addDefEq ci'.toDefEq := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have ⟨hwfE, hcf⟩ := VDefVal.addDefEq_wf hwf hu hci hadd
  replace href := href.mono (hle.trans le)
  refine congr_head hwfE (fun k Γ => ?_) href hcf (href.1.defeqU_l hwfE trivial hcf.symm)
  exact (hprim.natLitT henv.orderedStrong hnat k Γ).mono (hle.trans le)
