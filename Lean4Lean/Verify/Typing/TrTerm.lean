import Lean4Lean.Verify.Typing.Lemmas

/-!
# A typed builder for translated terms

`TrExprS.app`'s two side conditions are exactly a `HasType` for the function and a `HasType` for
the argument -- the same data a typed term bundle carries anyway. Bundling them means the
translation and the typing of a checker expression come out *by construction*, rather than being
threaded by hand at every node.

The bundle is indexed by the source expression, so the term the checker built fixes the goal and
`tgt` is an output. Everything the primitive checker probes is an application spine over opaque
atoms -- the definition's value, the constructors, the probe variables -- so `app'` plus the
three leaf constructors below cover it.
-/

namespace Lean4Lean

open Lean (Expr Name BinderInfo)

/-- A source expression, its translation, and a type for the translation. -/
structure TrTerm (env : VEnv) (Us : List Name) (Δ : VLCtx) (src : Expr) (A : VExpr) where
  tgt : VExpr
  trS : TrExprS env Us Δ src tgt
  hasType : env.HasType Us.length Δ.toCtx tgt A

/-- A source expression and its translation, known to be a type. -/
structure TrTy (env : VEnv) (Us : List Name) (Δ : VLCtx) (src : Expr) where
  tgt : VExpr
  trS : TrExprS env Us Δ src tgt
  isType : env.IsType Us.length Δ.toCtx tgt

/-! ### Leaves

The two facts every probe needs about its atoms: a globally closed translation transports into
whatever local context the probe variables have built up, and a probe variable resolves to the
`.bvar 0` its binder introduced. -/

/-- A `vlam` binder's own variable. `VLocalDecl.type` lifts, so the type comes back as `ty.lift`;
for the closed types the primitives use that is `ty` itself. -/
@[simp] theorem VLCtx.find?_vlam_self {fv : Lean.FVarId} {deps ty} {Δ : VLCtx} :
    VLCtx.find? ((some (fv, deps), .vlam ty) :: Δ) (.inr fv) = some (.bvar 0, ty.lift) := by
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]

/-- Looking past a `vlam` binder for someone else's variable: the answer is the tail's, lifted
by the binder's depth. This is what a probe variable from an *earlier* `withLocalDecl` needs. -/
theorem VLCtx.find?_vlam_ne {fv fv' : Lean.FVarId} {deps ty e A} {Δ : VLCtx}
    (hne : (fv == fv') = false) (h : Δ.find? (.inr fv') = some (e, A)) :
    VLCtx.find? ((some (fv, deps), .vlam ty) :: Δ) (.inr fv') = some (e.lift, A.lift) := by
  simp [VLCtx.find?, VLCtx.next, hne, h, VLocalDecl.depth]

/-- Looking past an *anonymous* `vlam` binder -- the one a `dite` branch's lambda introduces --
for a probe variable: same as `find?_vlam_ne`, but there is no name to be distinct from. -/
theorem VLCtx.find?_bvar_ne {fv : Lean.FVarId} {ty e A} {Δ : VLCtx}
    (h : Δ.find? (.inr fv) = some (e, A)) :
    VLCtx.find? ((none, .vlam ty) :: Δ) (.inr fv) = some (e.lift, A.lift) := by
  simp [VLCtx.find?, VLCtx.next, h, VLocalDecl.depth]

/-- A translation established at the empty local context holds in any well-formed one, provided
its target is closed -- which it is for a definition's value. -/
theorem TrExprS.of_nil (henv : env.WF) (hbv : Δ.NoBV) (hΔ : Δ.WF env Us.length)
    (hc : e'.ClosedN) (H : TrExprS env Us [] e e') : TrExprS env Us Δ e e' := by
  have := H.weakFV henv (VLCtx.FVLift.from_nil hbv) hΔ
  rwa [hc.liftN_eq (Nat.zero_le _)] at this

/-- Package an already-established translation and typing. This is how an *opaque* atom enters:
the definition's value arrives as a `TrExprS` from the body check, and nothing further is ever
known about it. -/
def TrTerm.of {src : Expr} {tgt A : VExpr}
    (trS : TrExprS env Us Δ src tgt) (hasType : env.HasType Us.length Δ.toCtx tgt A) :
    TrTerm env Us Δ src A := ⟨tgt, trS, hasType⟩

/-- The definition's value as a bundle, at any local context the probes have built up. Every
primitive branch needs exactly this, so the `of_nil`/`weak0`/`ClosedN` plumbing lives here. -/
def TrTerm.of_nil' (henv : env.WF) (hbv : Δ.NoBV) (hΔ : Δ.WF env Us.length)
    {e : Expr} {e' A : VExpr}
    (H : TrExprS env Us [] e e') (hT : env.HasType Us.length [] e' A) :
    TrTerm env Us Δ e A :=
  .of (H.of_nil henv hbv hΔ ((hT.closedN' henv.ordered.closed trivial).1))
    (VEnv.HasType.weak0 henv.ordered hT)

def TrTerm.cast (h : T = T') (H : TrTerm env Us Δ e T) : TrTerm env Us Δ e T' :=
  { H with hasType := h ▸ H.hasType }

/-- `Nat.zero` and `Nat.succ` as bundles, so branches do not repeat the `.1`/`.2` split. -/
def TrTerm.natZero (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) :
    TrTerm env Us Δ (.const ``Nat.zero []) .nat :=
  .of (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2

def TrTerm.boolLit (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) (b : Bool) :
    TrTerm env Us Δ (Lean.toExpr b) .bool :=
  .of (TrExprS.boolLit hprim hbool b).1 (TrExprS.boolLit hprim hbool b).2

def TrTerm.natSucc (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) :
    TrTerm env Us Δ (.const ``Nat.succ []) (.forallE .nat .nat) :=
  .of (TrExprS.natSucc hprim hnat).1 (TrExprS.natSucc hprim hnat).2

/-- A primitive used as an *operator* -- `Nat.pred` in `Nat.sub`'s recurrence, `Nat.add` in
`Nat.mul`'s -- enters as a bundle here. Unlike `Nat.zero`/`Nat.succ` these are not constructors,
so the typing comes from the typing clause of the primitive's reflection rather than from `Nat`'s
presence; the translation then reads the arity off the recorded type, as `trNat` does for `Nat`.
`instL` moves the typing to the level context the probes run in, which is only propositionally
empty, and the `by simp` default discharges it for the closed arrow types the primitives use. -/
theorem TrExprS.ofConst (henv : env.OrderedStrong) (hT : env.HasType 0 [] (.const c []) A)
    (hA : A.instL [] = A := by simp [VExpr.instL, VExpr.nat]) :
    TrExprS env Us Δ (.const c []) (.const c []) ∧
    env.HasType Us.length Δ.toCtx (.const c []) A := by
  obtain ⟨_, hci, -, hlen⟩ := hT.const_inv henv trivial
  exact ⟨.const hci rfl hlen, (hA ▸ hT.instL (ls := []) nofun).weak0 henv⟩

def TrTerm.ofConst (henv : env.OrderedStrong) (hT : env.HasType 0 [] (.const c []) A)
    (hA : A.instL [] = A := by simp [VExpr.instL, VExpr.nat]) :
    TrTerm env Us Δ (.const c []) A :=
  .of (TrExprS.ofConst henv hT hA).1 (TrExprS.ofConst henv hT hA).2

/-- Weaken a bundle past a freshly introduced binder. A probe variable from an earlier
`withLocalDecl` needs this once the next binder is open: its translation gains a lift, which for
the closed types the primitives use is the identity. -/
def TrTerm.wk (henv : env.WF) {fv deps ty} {e : Expr} {A : VExpr}
    (hΔ' : VLCtx.WF env Us.length ((some (fv, deps), .vlam ty) :: Δ))
    (h : TrTerm env Us Δ e A) :
    TrTerm env Us ((some (fv, deps), .vlam ty) :: Δ) e A.lift :=
  ⟨h.tgt.lift,
   h.trS.weakFV henv (.skip_fvar _ _ .refl) hΔ',
   h.hasType.weakN henv.ordered (VLCtx.FVLift.skip_fvar (fv, deps) (.vlam ty) .refl).toCtx⟩

def TrTerm.app {f a : Expr} {A B : VExpr}
    (hf : TrTerm env Us Δ f (.forallE A B)) (ha : TrTerm env Us Δ a A) :
    TrTerm env Us Δ (.app f a) (B.inst ha.tgt) :=
  ⟨.app hf.tgt ha.tgt,
   .app hf.hasType ha.hasType hf.trS ha.trS,
   .app hf.hasType ha.hasType⟩

/-- The non-dependent case, which is all the primitive probes need: every codomain there is a
closed constant, so `B.inst _` is `B` by `rfl`. -/
def TrTerm.app' {f a : Expr} {A B B' : VExpr}
    (hf : TrTerm env Us Δ f (.forallE A B)) (ha : TrTerm env Us Δ a A)
    (hB : B.inst ha.tgt = B' := by rfl) : TrTerm env Us Δ (.app f a) B' :=
  ⟨.app hf.tgt ha.tgt,
   .app hf.hasType ha.hasType hf.trS ha.trS,
   hB ▸ VEnv.HasType.app hf.hasType ha.hasType⟩

/-- A probe variable introduced by `withLocalDecl`. -/
def TrTerm.fvar {fv : Lean.FVarId} {e A : VExpr}
    (h : Δ.find? (.inr fv) = some (e, A))
    (hT : env.HasType Us.length Δ.toCtx e A) :
    TrTerm env Us Δ (.fvar fv) A := ⟨e, .fvar h, hT⟩

/-- A constant with no universe parameters, e.g. the `Nat` constructors. -/
def TrTerm.const0 {c : Name} {ci : VConstant} {A : VExpr}
    (h : env.constants c = some ci) (huv : ci.uvars = 0)
    (hT : env.HasType Us.length Δ.toCtx (.const c []) A) :
    TrTerm env Us Δ (.const c []) A :=
  ⟨.const c [], .const h rfl huv.symm, hT⟩

/-- The shape of every binary `Nat` probe: an opaque head applied to two `Nat` arguments.
`mkApp2 f a b` is `.app (.app f a) b` definitionally, so the source index matches the checker's
expression by `rfl`. -/
def TrTerm.natBinApp {f a b : Expr} {C : VExpr}
    (hf : TrTerm env Us Δ f (.forallE .nat (.forallE .nat C)))
    (ha : TrTerm env Us Δ a .nat) (hb : TrTerm env Us Δ b .nat)
    (h1 : (VExpr.forallE .nat C).inst ha.tgt = .forallE .nat C := by rfl)
    (h2 : C.inst hb.tgt = C := by rfl) :
    TrTerm env Us Δ (Lean.mkApp2 f a b) C := (hf.app' ha h1).app' hb h2

/-- The `Bool`-argument twin, for the operator the bitwise operations probe. -/
def TrTerm.boolBinApp {f a b : Expr} {C : VExpr}
    (hf : TrTerm env Us Δ f (.forallE .bool (.forallE .bool C)))
    (ha : TrTerm env Us Δ a .bool) (hb : TrTerm env Us Δ b .bool)
    (h1 : (VExpr.forallE .bool C).inst ha.tgt = .forallE .bool C := by rfl)
    (h2 : C.inst hb.tgt = C := by rfl) :
    TrTerm env Us Δ (Lean.mkApp2 f a b) C := (hf.app' ha h1).app' hb h2

/-- Likewise for a unary probe (`Nat.pred`, `Nat.succ` applied to a probe variable). -/
def TrTerm.natUnApp {f a : Expr}
    (hf : TrTerm env Us Δ f (.forallE .nat .nat)) (ha : TrTerm env Us Δ a .nat) :
    TrTerm env Us Δ (Lean.mkApp f a) .nat := hf.app' ha

def TrTy.of {src : Expr} {tgt : VExpr}
    (trS : TrExprS env Us Δ src tgt) (isType : env.IsType Us.length Δ.toCtx tgt) :
    TrTy env Us Δ src := ⟨tgt, trS, isType⟩

/-- `mdata` is erased by translation, so it passes straight through. This is what absorbs the
`@&` borrow annotations on the primitives' declared types. -/
def TrTy.mdata {d} {e : Expr} (h : TrTy env Us Δ e) : TrTy env Us Δ (.mdata d e) :=
  ⟨h.tgt, .mdata h.trS, h.isType⟩

def TrTerm.mdata {d} {e : Expr} {A : VExpr} (h : TrTerm env Us Δ e A) :
    TrTerm env Us Δ (.mdata d e) A := ⟨h.tgt, .mdata h.trS, h.hasType⟩

def TrTerm.lam {n : Name} {ty body : Expr} {bi : BinderInfo} {B : VExpr}
    (hty : TrTy env Us Δ ty)
    (hb : TrTerm env Us ((none, .vlam hty.tgt) :: Δ) body B) :
    TrTerm env Us Δ (.lam n ty body bi) (.forallE hty.tgt B) :=
  ⟨.lam hty.tgt hb.tgt,
   .lam hty.isType hty.trS hb.trS,
   .lam hty.isType.choose_spec hb.hasType⟩

def TrTy.forallE {n : Name} {ty body : Expr} {bi : BinderInfo}
    (hty : TrTy env Us Δ ty) (hb : TrTy env Us ((none, .vlam hty.tgt) :: Δ) body) :
    TrTy env Us Δ (.forallE n ty body bi) :=
  ⟨.forallE hty.tgt hb.tgt,
   .forallE hty.isType hb.isType hty.trS hb.trS,
   _, .forallEDF hty.isType.choose_spec hb.isType.choose_spec⟩
