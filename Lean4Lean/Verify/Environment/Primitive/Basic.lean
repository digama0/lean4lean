import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Primitive
import Lean4Lean.Environment

/-!
Vocabulary shared by the whole primitive-recognizer verification: lambda telescopes, the ground
judgements its statements are eventually about, and the extension a ground judgement is read in.
Nothing here mentions a particular primitive.
-/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- A reserved primitive name present in the real environment is present in the model: the
name is reserved, so `safePrimitives` says the declaration is safe, and `TrEnv.find?_iff` then
applies. Every primitive branch needs this for its prerequisite constants. -/
theorem TypeChecker.VContext.contains_primitive {c : VContext}
    (hs : c.safety = .safe) (h : c.env.contains n)
    (hp : Environment.primitives.contains n := by
      simp [Environment.primitives, NameSet.contains, NameSet.ofList]) :
    c.venv.contains n := by
  rw [Kernel.Environment.contains, SMap.find?_isSome] at h
  obtain ⟨ci, hci⟩ : ∃ ci, c.env.find? n = some ci := by
    rw [Kernel.Environment.find?, (c.trenv).map_wf.find?'_eq_find?]
    exact Option.isSome_iff_exists.1 h
  refine c.trenv.find?_iff.1 ⟨ci, hci, ?_⟩
  rw [hs, (c.safePrimitives hci hp).1]; exact DefinitionSafety.le_rfl

/-- A reflected binary `Nat` primitive computes at literals, in whatever context the caller is
in. `HasPrimitives` records reflection at `0 []`, which is where the level instantiation and
`weak0` come from; every branch whose recurrence applies another primitive to its arguments
needs it at the context its probes have reached. -/
theorem _root_.Lean4Lean.VEnv.ReflectsNatNatNat.applyLit {env : VEnv} {fc : Name}
    {f : Nat → Nat → Nat} (henv : env.Ordered) (H : env.ReflectsNatNatNat fc f)
    (hfc : env.contains fc) (a b : Nat) {U} {Γ : List VExpr} :
    env.IsDefEqU U Γ (((VExpr.const fc []).app (.natLit a)).app (.natLit b)) (.natLit (f a b)) := by
  obtain ⟨_, h⟩ := (H hfc).2 a b
  have h := (h.instL (ls := []) nofun).weak0 (U := U) (Γ := Γ) henv
  simp [VExpr.instL] at h
  exact ⟨_, h⟩

theorem TypeChecker.VContext.natBinLit {c : VContext} {fc : Name} {f : Nat → Nat → Nat}
    (H : c.venv.ReflectsNatNatNat fc f) (hfc : c.venv.contains fc) (a b : Nat) :
    c.IsDefEqU (((VExpr.const fc []).app (.natLit a)).app (.natLit b)) (.natLit (f a b)) :=
  H.applyLit c.Ewf.ordered hfc a b

/-- The `Bool`-valued counterpart, for the decision procedures a `Condition` runs on: a
`reflectNatNat` condition decides by `Nat.ble` or `Nat.beq`, and `WF_ite`/`WF_dite` only fire
once that decision is known to be a literal. -/
theorem TypeChecker.VContext.natBinLitBool {c : VContext} {fc : Name} {f : Nat → Nat → Bool}
    (H : c.venv.ReflectsNatNatBool fc f) (hfc : c.venv.contains fc) (a b : Nat) :
    c.IsDefEqU (((VExpr.const fc []).app (.natLit a)).app (.natLit b)) (.boolLit (f a b)) := by
  obtain ⟨_, h⟩ := (H hfc).2 a b
  have h := (h.instL (ls := []) nofun).weak0 (U := c.lparams.length) (Γ := c.vlctx.toCtx)
    c.Ewf.ordered
  simp [VExpr.instL] at h
  exact ⟨_, h⟩

/-- Introduce a `Nat`-typed probe variable. Every primitive branch does this once or twice, and
its two side conditions -- `Nat`'s translation, and that it is a type -- are always the same. -/
theorem TypeChecker.M.WF.withNatProbe {c : VContext} {m : MLCtx} [cwf : c.MLCWF m]
    {s₀ s : VState} {α} {f : Expr → M α} {Q} {name : Name}
    (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat) (hs : s₀ ≤ s)
    (H : ∀ id, let m' := m.vlam id name q(Nat) .nat .default
      ∀ cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
        let : TrTerm c.venv c.lparams m'.vlctx (.fvar id) .nat :=
          .fvar (VLCtx.find?_vlam_self (ty := .nat)) (.bvar .zero)
        M.WF (c.withMLC m' (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name .default q(Nat) f).WF (c.withMLC m) s Q :=
  .withLocalDecl (hprim.trNat c.Ewf.orderedStrong hnat)
    (hprim.natIsType c.Ewf.orderedStrong hnat (c.withMLC m).Δwf.toCtx) hs H

/-- The `Bool` counterpart, for the operator the bitwise operations probe. -/
theorem TypeChecker.M.WF.withBoolProbe {c : VContext} {m : MLCtx} [cwf : c.MLCWF m]
    {s₀ s : VState} {α} {f : Expr → M α} {Q} {name : Name}
    (hprim : c.venv.HasPrimitives) (hbool : c.venv.contains ``Bool) (hs : s₀ ≤ s)
    (H : ∀ id, let m' := m.vlam id name q(Bool) .bool .default
      ∀ cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
        let : TrTerm c.venv c.lparams m'.vlctx (.fvar id) .bool :=
          .fvar (VLCtx.find?_vlam_self (ty := .bool)) (.bvar .zero)
        M.WF (c.withMLC m' (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name .default q(Bool) f).WF (c.withMLC m) s Q :=
  .withLocalDecl (hprim.trBool c.Ewf.orderedStrong hbool)
    (hprim.boolIsType c.Ewf.orderedStrong hbool (c.withMLC m).Δwf.toCtx) hs H

/-- Application to a list of arguments, leftmost-first: the order `fvs` and a lambda telescope
already use. Everything the recognizer hands back is closed and abstracted over its telescope, so
arguments are *applied* rather than substituted, and no de Bruijn renumbering is involved. -/
def VExpr.appN (e : VExpr) : List VExpr → VExpr
  | [] => e
  | a :: as => (e.app a).appN as

@[simp] theorem VExpr.appN_nil (e : VExpr) : e.appN [] = e := rfl

theorem VExpr.insts_appN (g : List VExpr) : ∀ (e : VExpr) as,
    (e.appN as).insts g = (e.insts g).appN (as.map (·.insts g))
  | _, [] => rfl
  | e, a :: as => by simp [VExpr.appN, insts_appN g (e.app a) as]

theorem VExpr.subst_appN (γ : VExpr.Subst) : ∀ (e : VExpr) as,
    (e.appN as).subst γ = (e.subst γ).appN (as.map (·.subst γ))
  | _, [] => rfl
  | e, a :: as => by simp [VExpr.appN, subst_appN γ (e.app a) as]

/-! ### Lambda telescopes

A telescope of binders is opened by `lambdaTelescope` and closed again by giving each binder a
value. Both directions are needed: the recognizer works under the open telescope, while the
statements it feeds are about the value applied to ground arguments. `lams_appN` below is the
bridge, and the arguments' typing -- which is what makes the closing a `VEnv.Ctx.SubstEq` -- is not an
assumption but inversion of the application's own well-formedness. -/

/-- A lambda telescope over a list of domains, outermost first: the order `appN` applies its
arguments in and `insts` substitutes them. -/
def VExpr.lams : List VExpr → VExpr → VExpr
  | [], e => e
  | A :: As, e => .lam A (VExpr.lams As e)

@[simp] theorem VExpr.lams_nil (e : VExpr) : VExpr.lams [] e = e := rfl
@[simp] theorem VExpr.lams_cons (A As e) :
    VExpr.lams (A :: As) e = .lam A (VExpr.lams As e) := rfl

/-- The lifted domains, named. `liftN_lams` below only records how many there are, which is all
the closing lemmas need; a *caller* that has to type its own arguments against them needs them
by name, and each is lifted at its own depth. -/
theorem VExpr.liftN_lams' : ∀ (As : List VExpr) (e : VExpr) (n k : Nat),
    (VExpr.lams As e).liftN n k =
      VExpr.lams (As.mapIdx fun i A => A.liftN n (k + i)) (e.liftN n (k + As.length))
  | [], _, _, _ => rfl
  | A :: As, e, n, k => by
    have hk : k + 1 + As.length = k + (A :: As).length := by simp; omega
    have hfun : (fun (i : Nat) (B : VExpr) => VExpr.liftN n B (k + 1 + i))
        = (fun i B => VExpr.liftN n B (k + (i + 1))) := by funext i B; congr 1; omega
    simp only [VExpr.lams_cons, VExpr.liftN, VExpr.liftN_lams' As e n (k+1), hk,
      List.mapIdx_cons, Nat.add_zero, hfun]

/-- Lifting a telescope of `Nat`s changes nothing: `Nat` is closed, so the per-binder depths the
lift threads through `mapIdx` are all absorbed. -/
theorem List.mapIdx_replicate_nat (f : Nat → VExpr → VExpr) (hf : ∀ i, f i VExpr.nat = VExpr.nat) :
    ∀ len, (List.replicate len VExpr.nat).mapIdx f = List.replicate len VExpr.nat
  | 0 => rfl
  | len+1 => by
    simp [List.replicate_succ, List.mapIdx_cons, hf,
      List.mapIdx_replicate_nat (fun i => f (i+1)) (fun i => hf (i+1)) len]

/-- Every list of types is some `VLCtx`'s context. Facts stated only at a `VLCtx` -- `natIsType`
above all -- transfer to an arbitrary context through this. -/
def VLCtx.ofCtx : List VExpr → VLCtx
  | [] => []
  | A :: Γ => (none, .vlam A) :: VLCtx.ofCtx Γ

@[simp] theorem VLCtx.toCtx_ofCtx : ∀ Γ : List VExpr, (VLCtx.ofCtx Γ).toCtx = Γ
  | [] => rfl
  | A :: Γ => congrArg (A :: ·) (VLCtx.toCtx_ofCtx Γ)

theorem VEnv.HasPrimitives.boolIsType' {env : VEnv} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hbool : env.contains ``Bool) {Us : List Name} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType Us.length)) : env.IsType Us.length Γ VExpr.bool :=
  VLCtx.toCtx_ofCtx Γ ▸ hprim.boolIsType (Δ := VLCtx.ofCtx Γ) henv hbool (by simpa using hΓ)

theorem VEnv.HasPrimitives.natIsType' {env : VEnv} (henv : env.OrderedStrong)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) {Us : List Name} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType Us.length)) : env.IsType Us.length Γ VExpr.nat :=
  VLCtx.toCtx_ofCtx Γ ▸ hprim.natIsType (Δ := VLCtx.ofCtx Γ) henv hnat (by simpa using hΓ)

/-- A substitution does not touch a closed term, at the depth the recognizer works at. -/
theorem _root_.Lean4Lean.VExpr.ClosedN.subst_eq' {e : VExpr} {σ : VExpr.Subst}
    (h : e.ClosedN) : e.subst σ = e := h.subst_eq .zero

/-- The context an all-`Nat` telescope opens is well formed. -/
theorem _root_.Lean4Lean.OnCtx.natTelescope {env : VEnv}
    (hnat : ∀ Γ', OnCtx Γ' (env.IsType U) → env.IsType U Γ' VExpr.nat)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ len : Nat, OnCtx (List.replicate len VExpr.nat ++ Γ) (env.IsType U)
  | 0 => hΓ
  | len+1 => by
    have h := OnCtx.natTelescope hnat hΓ len
    exact show OnCtx (VExpr.nat :: _) _ from ⟨h, hnat _ h⟩

/-- Lifting through an all-`Nat` telescope: the domains are closed, so they are unchanged and the
only shift is in the depth. -/
theorem Ctx.LiftN.natTelescope {n k Γ Γ'} (W : Ctx.LiftN n k Γ Γ') : ∀ len : Nat,
    Ctx.LiftN n (k + len) (List.replicate len VExpr.nat ++ Γ)
      (List.replicate len VExpr.nat ++ Γ')
  | 0 => W
  | len+1 => by
    have h := (Ctx.LiftN.natTelescope W len).succ (A := VExpr.nat)
    simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm 1] using h

/-- A lifted lambda telescope is again a lambda telescope of the same length. The domains change
-- each is lifted at its own depth -- but nothing downstream looks at them, only at how many there
are, so an existential is enough and avoids indexing the list. -/
theorem VExpr.liftN_lams : ∀ (As : List VExpr) (e : VExpr) (n k : Nat),
    ∃ As', (VExpr.lams As e).liftN n k = VExpr.lams As' (e.liftN n (k + As.length)) ∧
      As'.length = As.length
  | [], _, _, _ => ⟨[], rfl, rfl⟩
  | A :: As, e, n, k => by
    obtain ⟨As', h, hlen⟩ := VExpr.liftN_lams As e n (k+1)
    refine ⟨A.liftN n k :: As', ?_, by simp [hlen]⟩
    have hk : k + 1 + As.length = k + (A :: As).length := by simp; omega
    simp only [VExpr.lams_cons, VExpr.liftN, h, hk]

theorem VExpr.lams_append : ∀ (As Bs : List VExpr) e,
    VExpr.lams (As ++ Bs) e = VExpr.lams As (VExpr.lams Bs e)
  | [], _, _ => rfl
  | _ :: As, Bs, e => by simp [VExpr.lams, lams_append As Bs e]

/-- The number of leading lambda binders, which is exactly how many `lambdaTelescope` opens: its
loop matches on `.lam` syntactically, with no `whnf` in between. A caller who wrote the measure
can therefore compute the telescope's arity by `rfl`, which is what lets them line their
recursion arguments up with it. -/
def _root_.Lean.Expr.lambdaArity : Expr → Nat
  | .lam _ _ b _ => b.lambdaArity + 1
  | _ => 0

theorem _root_.Lean.Expr.lambdaArity_eq_zero {e : Expr}
    (h : ∀ x d b bi, e ≠ .lam x d b bi) : e.lambdaArity = 0 := by
  cases e <;> simp only [Expr.lambdaArity]; cases h _ _ _ _ rfl

theorem _root_.List.Forall₂.map_right' {α β γ} {R : α → β → Prop} {S : α → γ → Prop} {f : β → γ}
    {l : List α} {l' : List β} (h : List.Forall₂ R l l') (H : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S l (l'.map f) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (H h) ih

theorem _root_.List.Forall₂.forall_left {α β} {R : α → β → Prop} {P : α → Prop}
    {l : List α} {l' : List β} (h : List.Forall₂ R l l') (H : ∀ {a b}, R a b → P a) :
    ∀ a ∈ l, P a := by
  induction h with
  | nil => exact nofun
  | cons h _ ih => rintro _ (_ | _) <;> [exact H h; exact ih _ ‹_›]

/-- `mkAppN` at a list, mirroring `VExpr.appN`: an induction on the list peels the *outermost*
argument, which is the direction `TrExprS.app` takes an application apart in. -/
def _root_.Lean.Expr.appN (e : Expr) : List Expr → Expr
  | [] => e
  | a :: as => (e.app a).appN as

theorem _root_.Lean.Expr.appN_eq_mkAppList (e : Expr) (as : List Expr) :
    e.appN as = e.mkAppList as := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih => exact ih (e.app a)

theorem _root_.Lean.Expr.mkAppN_eq (f : Expr) (as : Array Expr) :
    mkAppN f as = f.appN as.toList := by
  rw [show mkAppN f as = as.toList.foldl mkApp f from by simp [mkAppN]]
  generalize as.toList = l; induction l generalizing f <;> simp [Expr.appN, *]

theorem FVarsIn.appN {P} : ∀ {as : List Expr} {f : Expr},
    FVarsIn P f → (∀ a ∈ as, FVarsIn P a) → FVarsIn P (f.appN as) := by
  intro as
  induction as with
  | nil => intro _ h _; exact h
  | cons a as ih =>
    intro f h h2
    exact ih (show FVarsIn P (f.app a) by exact ⟨h, h2 _ (.head _)⟩) fun _ ha => h2 _ (.tail _ ha)

/-- The translation of an application is an application: no typing is needed to take one apart,
which is what lets `checkType`'s output be identified with the pieces it was built from. -/
theorem TrExprS.appN_inv : ∀ {as : List Expr} {f X}, TrExprS env Us Δ (f.appN as) X →
    ∃ X₀ xs, X = X₀.appN xs ∧ TrExprS env Us Δ f X₀ ∧ as.Forall₂ (TrExprS env Us Δ) xs := by
  intro as
  induction as with
  | nil => intro _ X h; exact ⟨X, [], rfl, h, .nil⟩
  | cons a as ih =>
    intro f X h
    obtain ⟨_, xs, rfl, hfa, has⟩ := ih h
    let .app _ _ hf ha := hfa
    exact ⟨_, _ :: xs, rfl, hf, .cons ha has⟩

/-- Two arguments off an application, which is the shape every condition's `prop` and `dec`, and
every reflected binary primitive, is applied at. -/
theorem TrExprS.app2_inv {f a b : Expr} {r : VExpr} (H : TrExprS env Us Δ (mkApp2 f a b) r) :
    ∃ f' a' b', TrExprS env Us Δ f f' ∧ TrExprS env Us Δ a a' ∧ TrExprS env Us Δ b b' ∧
      r = (f'.app a').app b' := by
  simp only [mkApp2] at H
  let .app _ _ hf hb := H; let .app _ _ hf ha := hf
  exact ⟨_, _, _, hf, ha, hb, rfl⟩

/-- A translation at the empty local context is a closed term. Everything a `Condition` records
is checked before any binder, so this is what says a closing leaves its pieces alone. -/
theorem TrExprS.closedN_nil {e : Expr} {e' : VExpr} (henv : env.Ordered)
    (H : TrExprS env Us [] e e') : e'.ClosedN := by
  have ⟨_, h⟩ : VExpr.WF env Us.length (VLCtx.toCtx []) e' := H.wf (Δ := []) henv trivial
  exact (h.closedN' henv.closed trivial).1

/-- An fvar's translation one binder further in is its own, lifted: an `fvar` translates by a
context lookup, and a `vlam` entry only shifts what the lookup finds. -/
theorem TrExprS.fvar_lift_uniq {fv : FVarId} {A t e : VExpr}
    (h₁ : TrExprS env Us Δ (.fvar fv) t)
    (h₂ : TrExprS env Us ((none, .vlam A) :: Δ) (.fvar fv) e) : e = t.lift := by
  let .fvar h₁ := h₁; let .fvar h₂ := h₂
  simp [VLCtx.find?, VLCtx.next, h₁, VLocalDecl.depth] at h₂
  exact h₂.1.symm

/-- A translation moved under one more bound-variable binder. `FVLift'` cannot do this -- it has
no `skip_bvar` -- but `BVLift` can, and at a context whose binders all name an fvar the source
term has no loose bound variables to shift. -/
theorem TrExprS.underBV {A : VExpr} {e : Expr} {e' : VExpr} (henv : env.Ordered) (hbv : Δ.NoBV)
    (H : TrExprS env Us Δ e e') : TrExprS env Us ((none, .vlam A) :: Δ) e e'.lift := by
  have h2 := TrExprS.weakBV henv (W := .skip (.vlam A) .refl) H
  rwa [Expr.liftLooseBVars_eq_self (hbv ▸ H.closed.looseBVarRange_le)] at h2

/-- A substitution extended by a telescope's values, in telescope order: the last value lands on
`bvar 0`, the innermost binder. -/
def _root_.Lean4Lean.VExpr.Subst.consN (σ : VExpr.Subst) : List VExpr → VExpr.Subst
  | [] => σ
  | v :: vs => (σ.cons v).consN vs

@[simp] theorem _root_.Lean4Lean.VExpr.Subst.consN_nil (σ : VExpr.Subst) : σ.consN [] = σ := rfl
@[simp] theorem _root_.Lean4Lean.VExpr.Subst.consN_cons (σ : VExpr.Subst) (v vs) :
    σ.consN (v :: vs) = (σ.cons v).consN vs := rfl

theorem List.Forall₂.append_inv {α β} {R : α → β → Prop} : ∀ {l₁ l₂ : List α} {m : List β},
    List.Forall₂ R (l₁ ++ l₂) m →
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _, h => by
    let .cons hx hxs := h
    obtain ⟨m₁, m₂, rfl, h₁, h₂⟩ := List.Forall₂.append_inv hxs
    exact ⟨_ :: m₁, m₂, rfl, .cons hx h₁, h₂⟩

theorem VExpr.appN_append : ∀ (e : VExpr) (as bs : List VExpr),
    e.appN (as ++ bs) = (e.appN as).appN bs
  | _, [], _ => rfl
  | e, a :: as, bs => VExpr.appN_append (e.app a) as bs

/-- A property of both members of a two-element list, which is what a probe's arguments are. -/
theorem List.forall_mem_pair {α} {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    ∀ t ∈ [a, b], P t := by simpa using ⟨ha, hb⟩

theorem List.Forall₂.snoc {α β} {R : α → β → Prop} {a b} (hab : R a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b])
  | [], _, h => by cases h; exact .cons hab .nil
  | _ :: _, _, h => by let .cons hx hl := h; exact .cons hx (List.Forall₂.snoc hab hl)

theorem List.Forall₂.rev {α β} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁.reverse l₂.reverse
  | [], _, h => by cases h; simp
  | _ :: _, _, h => by
    let .cons ha hl := h
    simpa using List.Forall₂.snoc ha (List.Forall₂.rev hl)

/-- A free variable's translation is determined by the context, since it is a `find?`. This is
what lets the arguments `checkType` handed back be identified with the telescope's own variables
without going through defeq. -/
theorem _root_.Lean4Lean.TrExprS.fvar_uniq {env : VEnv} {Us Δ} {fv : FVarId} {e₁ e₂ : VExpr}
    (h₁ : TrExprS env Us Δ (.fvar fv) e₁) (h₂ : TrExprS env Us Δ (.fvar fv) e₂) : e₁ = e₂ := by
  let .fvar h₁ := h₁; let .fvar h₂ := h₂
  exact congrArg Prod.fst (Option.some.inj (h₁.symm.trans h₂))

theorem List.Forall₂.fvars_uniq {env : VEnv} {Us Δ} : ∀ {l : List Expr} {xs ys : List VExpr},
    l.Forall₂ (TrExprS env Us Δ) xs → l.Forall₂ (TrExprS env Us Δ) ys →
    (∀ e ∈ l, ∃ fv, e = .fvar fv) → xs = ys
  | [], _, _, h₁, h₂, _ => by cases h₁; cases h₂; rfl
  | a :: l, _, _, h₁, h₂, hfv => by
    let .cons hx hxs := h₁; let .cons hy hys := h₂
    obtain ⟨_, rfl⟩ := hfv a (.head _)
    exact hx.fvar_uniq hy ▸ List.Forall₂.fvars_uniq hxs hys (fun e he => hfv e (.tail _ he)) ▸ rfl

theorem VExpr.Subst.consN_add : ∀ (vs : List VExpr) (σ : VExpr.Subst) (j),
    σ.consN vs (vs.length + j) = σ j
  | [], _, _ => by simp
  | v :: vs, σ, j => by
    have := VExpr.Subst.consN_add vs (σ.cons v) (j + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, VExpr.Subst.cons] using this

/-- A term lifted over the telescope and then closed at the telescope's arguments is just the
term closed: the lift is absorbed rather than cancelled one binder at a time. -/
theorem VExpr.liftN_subst_consN : ∀ {vs : List VExpr} {e : VExpr} {γ : VExpr.Subst},
    (VExpr.liftN vs.length e 0).subst (γ.consN vs) = e.subst γ
  | [], _, _ => by simp
  | v :: vs, e, γ => by
    rw [show (v :: vs).length = 1 + vs.length from by simp [Nat.add_comm], ← VExpr.liftN_liftN,
      VExpr.Subst.consN_cons,
      VExpr.liftN_subst_consN (vs := vs) (e := VExpr.liftN 1 e) (γ := γ.cons v)]
    simp [VExpr.lift_subst]

/-- Closing a telescope's variables is closing at its arguments: the variables translate to
`bvar 0, bvar 1, …` innermost-first, so read off in telescope order they are the reversed range,
and `consN` sends them to the arguments in that same order. -/
theorem VExpr.subst_consN_bvars : ∀ (vs : List VExpr) (σ : VExpr.Subst),
    ((List.range vs.length).map VExpr.bvar).reverse.map (VExpr.subst · (σ.consN vs)) = vs
  | [], _ => rfl
  | v :: vs, σ => by
    rw [show (v :: vs).length = vs.length + 1 from rfl, List.range_succ]
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    refine List.cons_eq_cons.2 ⟨?_, VExpr.subst_consN_bvars vs (σ.cons v)⟩
    simpa [VExpr.subst, VExpr.Subst.cons] using
      VExpr.Subst.consN_add vs (σ.cons v) 0

/-- Substituting under a binder and then instantiating that binder is the substitution itself:
each value is lifted and immediately cancelled. -/
theorem VExpr.subst_lift_tail_inst (e : VExpr) (σ : VExpr.Subst) (v : VExpr) :
    (e.subst σ.lift.tail).inst v = e.subst σ := by
  rw [VExpr.inst_eq, VExpr.subst_subst]
  congr 1
  funext i
  simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.tail, VExpr.Subst.one]

theorem VExpr.Subst.consN_append : ∀ (σ : VExpr.Subst) (l1 l2 : List VExpr),
    (σ.consN l1).consN l2 = σ.consN (l1 ++ l2)
  | _, [], _ => rfl
  | σ, a :: l1, l2 => VExpr.Subst.consN_append (σ.cons a) l1 l2

theorem VExpr.Subst.consN_append_singleton : ∀ (σ : VExpr.Subst) (l : List VExpr) (v : VExpr),
    σ.consN (l ++ [v]) = (σ.consN l).cons v
  | _, [], _ => rfl
  | σ, a :: l, v => VExpr.Subst.consN_append_singleton (σ.cons a) l v

@[simp] theorem VExpr.Subst.tail_cons {σ : VExpr.Subst} {v} : (σ.cons v).tail = σ := rfl

/-- Substituting under a binder and then instantiating it is substituting with the value in
place: this is the one-binder step of `lams_appN`. -/
theorem VExpr.Subst.lift_comp_one {σ : VExpr.Subst} {v} : σ.lift.comp (.one v) = σ.cons v := by
  funext i; cases i <;>
    simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons, VExpr.Subst.one, VExpr.lift_subst]

theorem OnCtx.of_append : ∀ {l Γ : List VExpr}, OnCtx (l ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _ :: l, _, h => OnCtx.of_append (l := l) h.1

/-- Both halves of an application are well formed. `app_inv` gives the typings, which is more
than a caller peeling a spine apart wants to name: this is the form that chains. -/
theorem VExpr.WF.app_inv₂ (henv : VEnv.OrderedStrong env) (hΓ : OnCtx Γ (env.IsType U)) {f a : VExpr}
    (H : VExpr.WF env U Γ (f.app a)) : VExpr.WF env U Γ f ∧ VExpr.WF env U Γ a :=
  let ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ; ⟨⟨_, hf⟩, ⟨_, ha⟩⟩

variable! (henv : VEnv.OrderedStrong env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem VExpr.WF.appN_inv : ∀ {vs : List VExpr} {e},
    VExpr.WF env U Γ (e.appN vs) → VExpr.WF env U Γ e
  | [], _, h => h
  | v :: vs, e, h =>
    let ⟨_, _, h, _⟩ := (VExpr.WF.appN_inv (vs := vs) (e := e.app v) h).app_inv henv hΓ
    ⟨_, h⟩

/-- Congruence for `appN`: the arguments' typings come from the application being well formed, so
no separate hypothesis about them is needed. -/
theorem VEnv.IsDefEqU.appN {env : VEnv} (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {vs : List VExpr} {f g}, env.IsDefEqU U Γ f g → VExpr.WF env U Γ (f.appN vs) →
      env.IsDefEqU U Γ (f.appN vs) (g.appN vs) := by
  intro vs
  induction vs with
  | nil => intro _ _ h _; exact h
  | cons v vs ih =>
    intro f g h hwf
    obtain ⟨A, B, hf, hv⟩ :=
      (VExpr.WF.appN_inv henv.orderedStrong hΓ (vs := vs) (e := f.app v) hwf).app_inv henv.orderedStrong hΓ
    exact ih ⟨_, (h.of_l henv hΓ hf).appDF hv⟩ hwf

/-- The arguments a lambda telescope is closed at, each typed at its own binder's domain under
the substitution built so far. This is the shape the induction over `lams` produces and consumes,
which is why it is a relation rather than a `Forall₂`: the domain of the `i`th binder is
substituted by `σ` extended with the first `i` arguments, not by `σ` alone. -/
inductive VExpr.ArgsTyped (env : VEnv) (U : Nat) (Γ₀ : List VExpr) :
    List VExpr → VExpr.Subst → List VExpr → Prop
  | nil : VExpr.ArgsTyped env U Γ₀ [] σ []
  | cons : env.HasType U Γ₀ v (A.subst σ) → VExpr.ArgsTyped env U Γ₀ As (σ.cons v) vs →
      VExpr.ArgsTyped env U Γ₀ (A :: As) σ (v :: vs)

/-- Arguments that are all naturals are `ArgsTyped` against an all-`Nat` telescope: `.nat` is
closed, so no substitution touches the domains. -/
theorem VExpr.ArgsTyped.natTelescope {env : VEnv} {U Γ₀} : ∀ {τ : List VExpr} {σ},
    (∀ t ∈ τ, env.HasType U Γ₀ t VExpr.nat) →
    VExpr.ArgsTyped env U Γ₀ (List.replicate τ.length VExpr.nat) σ τ
  | [], _, _ => .nil
  | t :: τ, σ, h => by
    refine .cons (A := VExpr.nat) (by simpa using h t (.head _)) ?_
    simpa using VExpr.ArgsTyped.natTelescope (τ := τ) (σ := σ.cons t)
      fun t' ht' => h t' (.tail _ ht')

/-- Contexts append: binders added *outside* a well-formed context leave it well formed, since
each type is closed at its own depth. -/
theorem OnCtx.append_right {env : VEnv} {U} (henv : env.Ordered) :
    ∀ {Γ₁ Γ₂ : List VExpr}, OnCtx Γ₁ (env.IsType U) → OnCtx Γ₂ (env.IsType U) →
      OnCtx (Γ₁ ++ Γ₂) (env.IsType U)
  | [], _, _, h2 => h2
  | A :: Γ₁, Γ₂, ⟨h1, u, hA⟩, h2 =>
    ⟨OnCtx.append_right henv h1 h2, u, by
      have h : env.HasType U (Γ₁ ++ Γ₂) A (.sort u) :=
        VEnv.IsDefEq.weakR henv (VEnv.CtxWF.closed henv h1) hA Γ₂
      exact h⟩

/-- The closing a telescope's arguments define. `lams_appN` builds this on the way to its beta
equation; pulled out, it is what lets an equation checked *under* a telescope of binders be closed
off at arguments for them -- which is how the reflection's checks reach their consumers. -/
theorem VExpr.ArgsTyped.substEq {env : VEnv} {U} {Γ₀ : List VExpr} :
    ∀ {As : List VExpr} {Γ σ vs}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VEnv.Ctx.SubstEq env U Γ₀ σ σ Γ → VExpr.ArgsTyped env U Γ₀ As σ vs →
      VEnv.Ctx.SubstEq env U Γ₀ (σ.consN vs) (σ.consN vs) (As.reverse ++ Γ) := by
  intro As
  induction As with
  | nil => intro _ _ _ _ hσ hargs; cases hargs; exact hσ
  | cons A As ih =>
    intro Γ σ vs hctx hσ hargs
    cases hargs with | cons hv hargs => ?_
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
      VExpr.Subst.consN_cons] at hctx ⊢
    obtain ⟨u, hAu⟩ : env.IsType U Γ A := (OnCtx.of_append hctx).2
    have hσ' : VEnv.Ctx.SubstEq env U Γ₀ (σ.cons _) (σ.cons _) (A :: Γ) := .cons hσ hAu hv
    exact ih hctx hσ' hargs

/-- A lambda telescope is well typed when its body is. Needed because closing a *second* term at
an already-built substitution cannot re-derive the binder typings from the application's own
well-typedness -- that is the obligation being avoided. -/
theorem VExpr.wf_lams {env : VEnv} {U} (henv : VEnv.WF env) :
    ∀ {As : List VExpr} {Γ e}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VExpr.WF env U (As.reverse ++ Γ) e → VExpr.WF env U Γ (VExpr.lams As e)
  | [], _, _, _, h => h
  | A :: As, Γ, e, hctx, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx h
    obtain ⟨u, hAu⟩ : env.IsType U Γ A := (OnCtx.of_append hctx).2
    obtain ⟨B, hB⟩ := VExpr.wf_lams henv (As := As) (Γ := A :: Γ) hctx h
    exact ⟨_, VEnv.HasType.lam hAu hB⟩

/-- The pi telescope matching `VExpr.lams`. -/
def VExpr.forallEs : List VExpr → VExpr → VExpr
  | [], e => e
  | A :: As, e => .forallE A (VExpr.forallEs As e)

@[simp] theorem VExpr.forallEs_nil (e : VExpr) : VExpr.forallEs [] e = e := rfl
@[simp] theorem VExpr.forallEs_cons (A As e) :
    VExpr.forallEs (A :: As) e = .forallE A (VExpr.forallEs As e) := rfl

/-- A lambda telescope's type is the pi telescope over the same domains. The typed counterpart of
`wf_lams`: same induction, but tracking the body's type rather than dropping it. -/
theorem VEnv.HasType.lams {env : VEnv} {U} (henv : VEnv.WF env) :
    ∀ {As : List VExpr} {Γ e T}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      env.HasType U (As.reverse ++ Γ) e T →
      env.HasType U Γ (VExpr.lams As e) (VExpr.forallEs As T)
  | [], _, _, _, _, h => h
  | A :: As, Γ, e, T, hctx, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx h
    obtain ⟨u, hAu⟩ : env.IsType U Γ A := (OnCtx.of_append hctx).2
    exact VEnv.HasType.lam hAu (VEnv.HasType.lams henv (As := As) (Γ := A :: Γ) hctx h)

/-- Eliminating a pi telescope: a term of that type, applied to arguments for the domains, has
the body's type closed at them. The counterpart of `HasType.lams`, and what types an application
whose head is only known through its declared type -- `lams_appN'` gives the *equation* between
the application and its beta-reduct, but not this. -/
theorem VEnv.HasType.appN_forallEs {env : VEnv} {U} {Γ : List VExpr} :
    ∀ {As : List VExpr} {T f vs σ}, VExpr.ArgsTyped env U Γ As σ vs →
      env.HasType U Γ f ((VExpr.forallEs As T).subst σ) →
      env.HasType U Γ (f.appN vs) (T.subst (σ.consN vs))
  | [], _, _, _, _, hargs, hf => by cases hargs; exact hf
  | A :: As, T, f, v :: vs, σ, .cons hv hargs, hf => by
    simp only [VExpr.forallEs_cons, VExpr.subst] at hf
    refine VEnv.HasType.appN_forallEs (σ := σ.cons v) hargs ?_
    have h := VEnv.HasType.app hf hv
    rwa [show ((VExpr.forallEs As T).subst σ.lift).inst _ = (VExpr.forallEs As T).subst (σ.cons _)
      from by rw [VExpr.inst_eq, VExpr.subst_subst, VExpr.Subst.lift_comp_one]] at h

/-- Congruence for a whole application spine, arguments included. `IsDefEqU.appN` covers only the
function; the typings each step needs come from the application's own well-typedness, the same
way `TrExprS.appN` gets them. -/
theorem VEnv.IsDefEqU.appN' {env : VEnv} {U Γ} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {xs ys : List VExpr} {f f'}, env.IsDefEqU U Γ f f' →
      List.Forall₂ (env.IsDefEqU U Γ) xs ys →
      VExpr.WF env U Γ (f.appN xs) →
      env.IsDefEqU U Γ (f.appN xs) (f'.appN ys)
  | [], _, _, _, hf, h, _ => by cases h; exact hf
  | x :: xs, y :: ys, f, f', hf, .cons hx hxs, hwf =>
    have ⟨_, _, hfT, hxT⟩ := (VExpr.WF.appN_inv (vs := xs) henv hΓ hwf).app_inv henv hΓ
    VEnv.IsDefEqU.appN' henv hΓ (f := f.app x) (f' := f'.app y)
      ⟨_, (hf.of_l henv hΓ hfT).appDF (hx.of_l henv hΓ hxT)⟩ hxs hwf

/-- The converse of `appN_inv`: an application's translation is the head's applied to the
arguments', *given* that the result is well typed. The typings `TrExprS.app` needs at each step
are exactly what `app_inv` reads back off that -- so a caller who knows only that the application
typechecks gets the translation for free. -/
theorem TrExprS.appN {env : VEnv} {Us Δ} (henv : VEnv.OrderedStrong env)
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    ∀ {as : List Expr} {xs : List VExpr} {f f'},
    TrExprS env Us Δ f f' → as.Forall₂ (TrExprS env Us Δ) xs →
    VExpr.WF env Us.length Δ.toCtx (f'.appN xs) →
    TrExprS env Us Δ (f.appN as) (f'.appN xs)
  | [], _, _, _, hf, h, _ => by cases h; exact hf
  | a :: _, x :: xs, f, f', hf, .cons hx hxs, hwf =>
    have hwf' := VExpr.WF.appN_inv (vs := xs) henv hΔ hwf
    have ⟨_, _, hfT, hxT⟩ := hwf'.app_inv henv hΔ
    TrExprS.appN henv hΔ (f := f.app a) (f' := f'.app x) (.app hfT hxT hf hx) hxs hwf

/-- Congruence in an application's argument. The one place the packed argument has to be
converted is here: the recognizer's checks are read at the binder, which closing sends to `P.arg`
on the nose, while the value chain ends at `a₀`, and only the packer's beta equation joins them. -/
theorem VEnv.IsDefEqU.app_arg {env : VEnv} {U Γ} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) {f a a' A B}
    (hf : env.HasType U Γ f (.forallE A B)) (ha : env.HasType U Γ a A)
    (h : env.IsDefEqU U Γ a a') : env.IsDefEqU U Γ (f.app a) (f.app a') :=
  ⟨_, .appDF hf (h.of_l henv hΓ ha)⟩

/-- A well-typed lambda telescope's domains are types in their own contexts -- the `OnCtx` that
closing it asks for. Read off the telescope itself rather than carried alongside it. -/
theorem VExpr.lams_ctx {env : VEnv} {U Γ} (henv : VEnv.OrderedStrong env) :
    ∀ {As : List VExpr} {e}, OnCtx Γ (env.IsType U) → VExpr.WF env U Γ (VExpr.lams As e) →
      OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], _, hΓ, _ => hΓ
  | A :: As, e, hΓ, h => by
    obtain ⟨hA, hbody⟩ := h.lam_inv henv hΓ
    simpa using VExpr.lams_ctx henv (Γ := _ :: Γ) ⟨hΓ, hA⟩ hbody

/-- A lambda telescope, closed off by `σ` and applied to as many arguments as it has binders. The
arguments extend `σ` to a closing of the telescope's own context, and the application is that
substitution.

`As` is in telescope order, so the context it opens is `As.reverse ++ Γ`; `OnCtx` there is what
an `MLCtx.WF` supplies, and it is needed because `VEnv.Ctx.SubstEq` asks for each domain to be a
type in *its own* context, which the closed-off application cannot say. -/
theorem VExpr.lams_appN {env : VEnv} {U} {Γ₀ : List VExpr} (henv : VEnv.WF env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {As : List VExpr} {Γ} (hctx : OnCtx (As.reverse ++ Γ) (env.IsType U))
    {σ} (hσ : VEnv.Ctx.SubstEq env U Γ₀ σ σ Γ)
    {vs e} (hlen : vs.length = As.length)
    (hwf : VExpr.WF env U Γ₀ (((VExpr.lams As e).subst σ).appN vs)) :
    VEnv.Ctx.SubstEq env U Γ₀ (σ.consN vs) (σ.consN vs) (As.reverse ++ Γ) ∧
    env.IsDefEqU U Γ₀ (((VExpr.lams As e).subst σ).appN vs) (e.subst (σ.consN vs)) ∧
    VExpr.ArgsTyped env U Γ₀ As σ vs := by
  induction As generalizing Γ σ hσ vs with
  | nil => cases List.eq_nil_of_length_eq_zero hlen; exact ⟨hσ, hwf, .nil⟩
  | cons A As ih
  let v :: vs := vs
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx ⊢
  obtain ⟨u, hAu⟩ : env.IsType U Γ A := (OnCtx.of_append hctx).2
  -- the head binder: invert the application, then read the domain off the lambda itself
  obtain ⟨A', B', hf, hv⟩ :=
    (VExpr.WF.appN_inv henv.orderedStrong hΓ₀ (vs := vs) hwf).app_inv henv.orderedStrong hΓ₀
  obtain ⟨⟨u₀, hAσ⟩, B₀, hX⟩ := hf.lam_inv henv.orderedStrong hΓ₀
  obtain ⟨⟨u₁, hAA'⟩, -⟩ := (hf.uniqU henv hΓ₀ (hAσ.lam hX)).forallE_inv henv hΓ₀
  have hv' : env.HasType U Γ₀ v (A.subst σ) := .defeqDF hAA' hv
  have hbeta : env.IsDefEq U Γ₀ ((VExpr.lams (A :: As) e).subst σ |>.app v)
      ((VExpr.lams As e).subst (σ.cons v)) (B₀.inst v) := by
    have h := VEnv.IsDefEq.beta hX hv'
    rwa [show ((VExpr.lams As e).subst σ.lift).inst v = (VExpr.lams As e).subst (σ.cons v) from
      by rw [VExpr.inst_eq, VExpr.subst_subst, VExpr.Subst.lift_comp_one]] at h
  have hcong := VEnv.IsDefEqU.appN henv hΓ₀ (vs := vs) ⟨_, hbeta⟩ hwf
  have hσ' : VEnv.Ctx.SubstEq env U Γ₀ (σ.cons v) (σ.cons v) (A :: Γ) := .cons hσ hAu hv'
  obtain ⟨hcl, heq, hargs⟩ := ih (Γ := A :: Γ) hctx hσ' (vs := vs) (by simpa using hlen)
    (hwf.imp fun _ h => VEnv.HasType.defeqU_l henv hΓ₀ hcong h)
  exact ⟨hcl, VEnv.IsDefEqU.trans henv hΓ₀ hcong heq, .cons hv' hargs⟩

/-- The beta equation of `lams_appN`, but consuming a closing that has already been built rather
than recovering it from the application's own well-typedness -- which is the obligation being
avoided. `hσm` pays for that once, for the measure; every other term closed at the same recursion
arguments (the packer above all) reuses the substitution and the argument typings it produced. -/
theorem VExpr.lams_appN' {env : VEnv} {U} {Γ₀ : List VExpr} (henv : VEnv.WF env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {As : List VExpr} {Γ} (hctx : OnCtx (As.reverse ++ Γ) (env.IsType U))
    {σ} (hσ : VEnv.Ctx.SubstEq env U Γ₀ σ σ Γ)
    {vs e} (hargs : VExpr.ArgsTyped env U Γ₀ As σ vs)
    (hwf : VExpr.WF env U (As.reverse ++ Γ) e) :
    VExpr.WF env U Γ₀ (((VExpr.lams As e).subst σ).appN vs) ∧
    env.IsDefEqU U Γ₀ (((VExpr.lams As e).subst σ).appN vs) (e.subst (σ.consN vs)) := by
  induction hargs generalizing Γ with
  | nil => exact ⟨.subst henv.orderedStrong hσ hwf, .subst henv.orderedStrong hσ hwf⟩
  | @cons v As vs A σ hv' hargs ih
  have hlamwf : VExpr.WF env U Γ₀ ((VExpr.lams (A :: As) e).subst σ) :=
    .subst henv.orderedStrong hσ (VExpr.wf_lams henv hctx hwf)
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx hwf
  obtain ⟨u, hAu⟩ : env.IsType U Γ A := (OnCtx.of_append hctx).2
  obtain ⟨⟨u₀, hAσ⟩, B₀, hX⟩ := hlamwf.lam_inv henv.orderedStrong hΓ₀
  have hbeta := VEnv.IsDefEq.beta hX hv'
  rw [VExpr.inst_eq, VExpr.subst_subst, VExpr.Subst.lift_comp_one] at hbeta
  have hσ' : VEnv.Ctx.SubstEq env U Γ₀ (σ.cons v) (σ.cons v) (A :: Γ) := .cons hσ hAu hv'
  obtain ⟨hwfIH, heq⟩ := ih hctx hσ' hwf
  have hcong := VEnv.IsDefEqU.appN henv hΓ₀ (vs := vs) ⟨_, hbeta.symm⟩ hwfIH
  exact ⟨hcong.symm.trans henv hΓ₀ hcong, hcong.symm.trans henv hΓ₀ heq⟩

/-! ### Ground judgements

What the recognizer's statements are eventually about: closed terms. `HasPrimitives` is a fact
about the empty context, and for `Nat.bitwise` the operator is a variable of the recognizer's own
context whose evaluation behaviour only exists once it is instantiated, so that context is closed
off with a substitution and everything below is stated at `[]`. -/

abbrev TypeChecker.VContext.HasType₀ (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length []
abbrev TypeChecker.VContext.IsDefEqU₀ (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length []
abbrev TypeChecker.VContext.WF₀ (c : VContext) : VExpr → Prop :=
  VExpr.WF c.venv c.lparams.length []

/-- `γ` closes the recognizer's context: a substitution into the *empty* context, taken as a
`VEnv.Ctx.SubstEq` with itself so that `nil` pins it to the identity when there is nothing to
close. -/
abbrev TypeChecker.VContext.Closing (c : VContext) (γ : VExpr.Subst) : Prop :=
  VEnv.Ctx.SubstEq c.venv c.lparams.length [] γ γ c.vlctx.toCtx

/-- The environment a ground judgement is read in. Every primitive but `Nat.bitwise` reads its
own: the operators a recurrence mentions are constants the branch guarded on, so the checking
environment already has them, and `self` is the extension taken.

`Nat.bitwise` cannot. Its operator is a *variable* of the recognizer's context, and the spec it
owes -- `ReflectsNatBitwise` -- is about every operator any later environment might supply, so
the substitution that instantiates that variable lands outside `c.venv`. Since the recognizer's
facts are `IsDefEqU`s, which are monotone, the fix is to read the closed layer in an arbitrary
well-formed extension rather than in `c.venv`: this is that extension. -/
structure TypeChecker.VContext.Ext (c : VContext) where
  venv : VEnv
  le : c.venv ≤ venv
  wf : venv.WF

/-- The checking environment itself, which is the extension every branch but `Nat.bitwise`
takes. Reducible, so that a statement read at `c.self` is the one read at `c` on the nose and
the branches that take it need no rewriting. -/
@[reducible] def TypeChecker.VContext.self (c : VContext) : c.Ext := ⟨c.venv, .rfl, c.Ewf⟩

/-- An extension is one of the environment, not of the context, so it transports along any change
of context that keeps the environment: opening a binder, or the `withMLC_self` a recognizer opens
with. The default `rfl` covers both, since `withMLC` is a structure update. -/
@[reducible] def TypeChecker.VContext.Ext.cast {c c' : VContext} (E : c.Ext)
    (h : c'.venv = c.venv := by rfl) : c'.Ext := ⟨E.venv, h ▸ E.le, E.wf⟩

abbrev TypeChecker.VContext.Ext.HasType₀ {c : VContext} (E : c.Ext) : VExpr → VExpr → Prop :=
  E.venv.HasType c.lparams.length []
abbrev TypeChecker.VContext.Ext.IsDefEqU₀ {c : VContext} (E : c.Ext) : VExpr → VExpr → Prop :=
  E.venv.IsDefEqU c.lparams.length []
abbrev TypeChecker.VContext.Ext.WF₀ {c : VContext} (E : c.Ext) : VExpr → Prop :=
  VExpr.WF E.venv c.lparams.length []

/-- `γ` closes the recognizer's context into the extension. At `c.self` this is `c.Closing`. -/
abbrev TypeChecker.VContext.Ext.Closing {c : VContext} (E : c.Ext) (γ : VExpr.Subst) : Prop :=
  VEnv.Ctx.SubstEq E.venv c.lparams.length [] γ γ c.vlctx.toCtx

/-- Reading an open judgement of the checking environment in the extension. -/
theorem TypeChecker.VContext.Ext.mono {c : VContext} (E : c.Ext) {U Γ e₁ e₂}
    (h : c.venv.IsDefEqU U Γ e₁ e₂) : E.venv.IsDefEqU U Γ e₁ e₂ := h.mono E.le

theorem TypeChecker.VContext.Ext.monoT {c : VContext} (E : c.Ext) {U Γ e A}
    (h : c.venv.HasType U Γ e A) : E.venv.HasType U Γ e A := h.mono E.le

theorem TypeChecker.VContext.Ext.monoW {c : VContext} (E : c.Ext) {U Γ e}
    (h : VExpr.WF c.venv U Γ e) : VExpr.WF E.venv U Γ e := let ⟨_, h⟩ := h; ⟨_, h.mono E.le⟩

theorem TypeChecker.VContext.Ext.monoIsType {c : VContext} (E : c.Ext) {U Γ A}
    (h : c.venv.IsType U Γ A) : E.venv.IsType U Γ A := let ⟨_, h⟩ := h; ⟨_, h.mono E.le⟩

theorem TypeChecker.VContext.Ext.monoCtx {c : VContext} (E : c.Ext) {U Γ}
    (h : OnCtx Γ (c.venv.IsType U)) : OnCtx Γ (E.venv.IsType U) :=
  h.mono (VEnv.IsType.mono E.le)

/-- A reflected binary `Nat` primitive at arguments that are worth literals, under a closing.

Containment comes from the translation rather than from a guard on the branch: a constant only
translates if it is in the environment, so a recurrence may name `Nat.add`, `Nat.div` or
`Nat.mod` without its recognizer having to check for them.

The arguments' values are asked for at *any* translation of them, so that nested applications
compose without a uniqueness side condition -- the packer a recursive call is applied to has
none. -/
theorem TypeChecker.VContext.Ext.natBinLitTr {c : VContext} (E : c.Ext) {Δ : VLCtx}
    {σ : VExpr.Subst} {C : Name} {F : Nat → Nat → Nat} {A B : Expr} {r : VExpr} (a b : Nat)
    (hrefl : c.venv.ReflectsNatNatNat C F)
    (hA : ∀ {A' : VExpr}, Lean4Lean.TrExprS c.venv c.lparams Δ A A' → E.WF₀ (A'.subst σ) →
      E.IsDefEqU₀ (A'.subst σ) (.natLit a))
    (hB : ∀ {B' : VExpr}, Lean4Lean.TrExprS c.venv c.lparams Δ B B' → E.WF₀ (B'.subst σ) →
      E.IsDefEqU₀ (B'.subst σ) (.natLit b))
    (hr : Lean4Lean.TrExprS c.venv c.lparams Δ (mkApp2 (.const C []) A B) r)
    (hwf : E.WF₀ (r.subst σ)) : E.IsDefEqU₀ (r.subst σ) (.natLit (F a b)) := by
  obtain ⟨_, _, _, hC, hA2, hB2, rfl⟩ := hr.app2_inv
  obtain ⟨rfl, -⟩ := hC.const0_inv (Us' := c.lparams) (Δ' := ([] : VLCtx))
  have hcont : c.venv.contains C := by cases hC with | const hci _ _ => exact ⟨_, hci⟩
  have hlit := E.mono (hrefl.applyLit c.Ewf.ordered hcont a b (U := c.lparams.length) (Γ := []))
  simp only [VExpr.subst] at hwf ⊢
  have pk : ∀ {f x : VExpr}, E.WF₀ (f.app x) → E.WF₀ f ∧ E.WF₀ x :=
    fun h => h.app_inv₂ E.wf.orderedStrong trivial
  refine .trans E.wf trivial ?_ hlit
  exact (VEnv.IsDefEqU.appN' E.wf trivial (xs := [_, _])
    (ys := [VExpr.natLit a, VExpr.natLit b]) ⟨_, ((pk (pk hwf).1).1).choose_spec⟩
    (.cons (hA hA2 (pk (pk hwf).1).2) (.cons (hB hB2 (pk hwf).2) .nil))
    (by simpa [VExpr.appN, VExpr.WF] using hwf) :)

/-! ### Telescopes

Counting arguments about `MLCtx`, used where a telescope's binders have to account for exactly
the context entries it opened. -/

/-- Dropping `n` binders removes at most `n` entries from the context: a `vlam` removes one and a
`vlet` none, because a let is inlined rather than bound. -/
theorem MLCtx.dropN_toCtx_length {n : Nat} {m : MLCtx} {hn : n ≤ m.length} :
    m.vlctx.toCtx.length ≤ n + (m.dropN n hn).vlctx.toCtx.length := by
  induction n generalizing m with | zero => simp | succ n ih
  match m, hn with
  | .vlam _ _ _ _ _ m₁, hn =>
    have := @ih m₁ (Nat.le_of_succ_le_succ hn)
    simp only [MLCtx.vlctx, VLCtx.toCtx, List.length_cons, MLCtx.dropN] at *; omega
  | .vlet _ _ _ _ _ _ m₁, hn =>
    have := @ih m₁ (Nat.le_of_succ_le_succ hn)
    simp only [MLCtx.vlctx, VLCtx.toCtx, MLCtx.dropN] at *; omega

/-- A telescope whose binders account for exactly the new context entries opens with a `vlam`.
Same counting argument as `mkLambda'_eq_lams`: a `vlet` contributes no entry, so it cannot be
among binders that contribute one each. Needed where a *single* binder has to be peeled -- the
recognizer's fuel variable, which `Step` must show the recursor does not depend on. -/
theorem MLCtx.head_vlam : ∀ {n : Nat} {m : MLCtx} {hn : n + 1 ≤ m.length} {Bs : List VExpr},
    Bs.length = n + 1 → m.vlctx.toCtx = Bs ++ (m.dropN (n + 1) hn).vlctx.toCtx →
    ∃ x nm ty tyv bi m', m = .vlam x nm ty tyv bi m'
  | _, .vlam .., _, _, _, _ => ⟨_, _, _, _, _, _, rfl⟩
  | n, .vlet .., hn, Bs, hlen, hctx => by
    simp only [MLCtx.vlctx, VLCtx.toCtx] at hctx
    have := MLCtx.dropN_toCtx_length (n := n) (hn := Nat.le_of_succ_le_succ hn)
    rw [hctx] at this; simp [hlen] at this; omega

/-- `mkLambda'` over a telescope whose binders account for exactly the `n` new context entries is
the plain `VExpr.lams` over those entries. The hypothesis is what rules out a `vlet` among them:
a let contributes no entry, so `n` binders that add `n` entries leaves no room for one. -/
theorem MLCtx.mkLambda'_eq_lams : ∀ {n : Nat} {m : MLCtx} {hn : n ≤ m.length} {Bs : List VExpr}
    {e' : VExpr}, Bs.length = n → m.vlctx.toCtx = Bs ++ (m.dropN n hn).vlctx.toCtx →
    m.mkLambda' n hn e' = VExpr.lams Bs.reverse e'
  | 0, _, _, Bs, _, hlen, _ => by cases List.eq_nil_of_length_eq_zero hlen; rfl
  | _+1, .vlam .., _, Bs, e', hlen, hctx => by
    obtain _ | ⟨B, Bs⟩ := Bs; · simp at hlen
    simp only [MLCtx.vlctx, VLCtx.toCtx, List.cons_append, List.cons.injEq] at hctx
    obtain ⟨rfl, hctx⟩ := hctx
    simp only [MLCtx.mkLambda', List.reverse_cons, VExpr.lams_append, VExpr.lams_cons,
      VExpr.lams_nil]
    exact MLCtx.mkLambda'_eq_lams (by simpa using hlen) hctx
  | n+1, .vlet .., hn, Bs, _, hlen, hctx => by
    simp only [MLCtx.vlctx, VLCtx.toCtx] at hctx
    have := MLCtx.dropN_toCtx_length (n := n) (hn := Nat.le_of_succ_le_succ hn)
    rw [hctx] at this; simp [hlen] at this; omega

/-- The translation side of the telescope invariant, as a bundle: the `Expr`-level facts are
`inferLambda.loop.WF`'s, but a caller that has to *close* the telescope needs its domains and its
variables' translations too, and threading eight hypotheses through `loop` one at a time is
unreadable. `As` is in telescope order, so the context the telescope opens is `As.reverse` on top
of `m₀`'s, and the variables translate to `bvar 0, bvar 1, ...` innermost-first -- which is the
order `arr.toList.reverse` is already in.

`lams` is stated with `MLCtx.mkLambda'`, the VExpr counterpart of the `MLCtx.mkLambda` the
`Expr`-level facts use, rather than `VExpr.lams As`: those agree only when every binder is a
`vlam`, which is true of `lambdaTelescope` but is not something the invariant should be quietly
assuming. `As` stays because closing the telescope goes through `VExpr.lams_appN`. -/
structure lambdaTelescope.Inv (c : VContext) (m₀ m : MLCtx) [c.MLCWF m] (arr : Array Expr)
    (n : Nat) (hn : n ≤ m.length) (As : List VExpr) (e₀' e' : VExpr) : Prop where
  len : As.length = n
  toCtx : m.vlctx.toCtx = As.reverse ++ m₀.vlctx.toCtx
  lift : VLCtx.FVLift m₀.vlctx m.vlctx 0 n 0
  vars : arr.toList.reverse.Forall₂ (c.withMLC m).TrExprS ((List.range n).map .bvar)
  lams : e₀' = m.mkLambda' n hn e'

/-- Every leading binder's type is literally `Nat`. The recursion arguments of a well-founded
primitive are naturals; a consumer that has to type its own arguments against the packer's domains
needs to know that, since otherwise those domains are opaque to it. This is a *hypothesis* of the
theorems below rather than a check in the recognizer: the caller wrote the measure, so it holds by
`rfl` there, and the checker's behaviour is unchanged. Syntactic, so the domains come out as `.nat`
on the nose rather than merely defeq to it. -/
def _root_.Lean.Expr.natBinderTypes : Expr → Bool
  | .lam _ d b _ => d == q(Nat) && b.natBinderTypes
  | _ => true

/-- Abstracting a variable cannot make a binder type into `Nat` that was not already: abstraction
only turns free variables into bound ones, and `Nat` contains neither. -/
theorem _root_.Lean.Expr.natBinderTypes_of_abstract1 {e : Expr} {x : FVarId} {k : Nat} :
    (e.abstract1 x k).natBinderTypes = true → e.natBinderTypes = true := by
  induction e generalizing k with
  | lam _ d b _ _ ihb =>
    simp only [Expr.abstract1, Expr.natBinderTypes, Bool.and_eq_true]
    rintro ⟨hd, hb⟩; refine ⟨?_, ihb hb⟩
    cases d <;> simp_all [Expr.abstract1, (· == ·), Expr.eqv']
    split at hd <;> simp_all [Expr.eqv']
  | _ => intro _; rfl

/-- The guard on the measure, read at the telescope: if the term the telescope built has all its
leading binder types `Nat`, then the context entries it opened are `.nat` on the nose. `mkLambda`
abstracts as it builds, which is why this needs `natBinderTypes_of_abstract1`. Unlike the other
telescope lemmas this one is about the recognizer's measure guard, so it lives here. -/
theorem MLCtx.mkLambda_natBinderTypes {env : VEnv} {Us : List Name} :
    ∀ {n : Nat} {m : MLCtx} {hn : n ≤ m.length} {X : Expr} {Bs : List VExpr},
      MLCtx.WF env Us m → Bs.length = n →
      m.vlctx.toCtx = Bs ++ (m.dropN n hn).vlctx.toCtx →
      (m.mkLambda n hn X).natBinderTypes = true →
      Bs = List.replicate n .nat ∧ X.natBinderTypes = true
  | 0, _, _, _, Bs, _, hlen, _, hX => ⟨by cases List.eq_nil_of_length_eq_zero hlen; rfl, hX⟩
  | _+1, .vlam _ _ ty tyv _ _, _, X, Bs, hwf, hlen, hctx, hX => by
    obtain _ | ⟨B, Bs⟩ := Bs; · simp at hlen
    simp only [MLCtx.vlctx, VLCtx.toCtx, List.cons_append, List.cons.injEq] at hctx
    obtain ⟨rfl, hctx⟩ := hctx
    obtain ⟨hBs, hX'⟩ := MLCtx.mkLambda_natBinderTypes hwf.1 (by simpa using hlen) hctx hX
    simp only [Expr.natBinderTypes, Bool.and_eq_true] at hX'
    obtain ⟨hty, hXab⟩ := hX'
    have htyS : TrExprS env Us _ (Expr.const ``Nat []) tyv := hwf.2.2.1.eqv hty
    let .const _ h2 _ := htyS
    cases h2
    exact ⟨by simp [hBs, List.replicate_succ, VExpr.nat], Expr.natBinderTypes_of_abstract1 hXab⟩
  | n+1, .vlet .., hn, _, Bs, _, hlen, hctx, _ => by
    simp only [MLCtx.vlctx, VLCtx.toCtx] at hctx
    have := MLCtx.dropN_toCtx_length (n := n) (hn := Nat.le_of_succ_le_succ hn)
    rw [hctx] at this; simp [hlen] at this; omega

theorem lambdaTelescope.loop.WF {c : VContext} {α} {k : Array Expr → Expr → M α}
    {Q : α → VState → Prop} {s₀ : VState} {m₀ : MLCtx} [c.MLCWF m₀] {e₀ : Expr} {e₀' : VExpr}
    (H : ∀ (fvs : Array Expr) {m' : MLCtx} [c.MLCWF m'] {s' : VState} {body} body'
      {n} (hn : n ≤ m'.length) {As}, s₀ ≤ s' → m'.dropN n hn = m₀ →
      fvs.toList.reverse = (m'.fvarRevList n hn).map .fvar → e₀ = m'.mkLambda n hn body →
      lambdaTelescope.Inv c m₀ m' fvs n hn As e₀' body' → e₀.lambdaArity = n →
      (c.withMLC m').TrExprS body body' → (k fvs body).WF (c.withMLC m') s' Q)
    (e : Expr) (arr : Array Expr) (m : MLCtx) [c.MLCWF m] (s : VState) (e' : VExpr)
    {n} (hn : n ≤ m.length) (harity : e₀.lambdaArity = n + e.lambdaArity)
    (hdrop : m.dropN n hn = m₀)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn (Expr.instantiateList e arr.toList.reverse))
    {As} (hinv : lambdaTelescope.Inv c m₀ m arr n hn As e₀' e')
    (hs : s₀ ≤ s) (he : (c.withMLC m).TrExprS (Expr.instantiateList e arr.toList.reverse) e') :
    (lambdaTelescope.loop k arr e).WF (c.withMLC m) s Q := by
  unfold lambdaTelescope.loop; split
  · rename_i body _
    revert hinv
    let .lam (ty' := domv) (body' := body') domty hdom hbody := Expr.instantiateList_lam ▸ he
    intro hinv
    rw [Expr.instantiateRev_eq_instantiateList]
    refine M.WF.withLocalDecl hdom domty hs fun fv cwf' s' hs' _ => ?_
    have hinst : Expr.instantiateList body ((arr.push (Expr.fvar fv)).toList.reverse)
        = (Expr.instantiateList body arr.toList.reverse 1).instantiate1' (.fvar fv) := by
      rw [show (arr.push (Expr.fvar fv)).toList.reverse
        = Expr.fvar fv :: arr.toList.reverse from by simp]
      exact (Expr.instantiateList_instantiate1_comm (a := .fvar fv) (by trivial)).symm
    refine lambdaTelescope.loop.WF H _ (arr.push (.fvar fv)) _ s' body'
      (Nat.succ_le_succ hn) (by simp only [Expr.lambdaArity] at harity ⊢; omega)
      (by simp [hdrop]) (by simp [harr]) ?_ (As := As ++ [domv]) ⟨?_, ?_, ?_, ?_, ?_⟩ hs' ?_
    · -- the abstraction the new binder adds cancels the instantiation, because the body's
      -- variables are the old context's and `withLocalDecl` handed back a fresh one
      have hcancel : Expr.abstract1 fv
          ((Expr.instantiateList body arr.toList.reverse 1).instantiate1' (.fvar fv))
          = Expr.instantiateList body arr.toList.reverse 1 :=
        FVarsIn.abstract_instantiate1 <| hbody.fvarsIn.mono <| by
          rintro _ h rfl; exact (cwf'.wf.tr.wf.2.1 _ _ rfl).1 h
      rw [he₀, hinst]; simp [Expr.instantiateList_lam, hcancel]
    · simp [hinv.len]
    · simp [VLCtx.toCtx, hinv.toCtx]
    · exact .skip_fvar _ _ hinv.lift
    · -- the new variable is `bvar 0` and the old ones move up one, which is what the range does
      rw [show (arr.push (Expr.fvar fv)).toList.reverse
            = Expr.fvar fv :: arr.toList.reverse from by simp,
        show (List.range (n+1)).map VExpr.bvar
            = .bvar 0 :: ((List.range n).map VExpr.bvar).map (VExpr.liftN 1 · 0) from by
          simp [List.range_succ_eq_map, List.map_map, Function.comp_def, VExpr.liftN]]
      exact .cons (.fvar VLCtx.find?_vlam_self) (hinv.vars.map_right' fun h =>
        h.weakFV c.Ewf.ordered (.skip_fvar _ _ .refl) cwf'.wf.tr.wf)
    · exact hinv.lams
    · rw [hinst]; exact hbody.inst_fvar c.Ewf.ordered cwf'.wf.tr.wf
  · simp only [Expr.instantiateRev_eq_instantiateList]
    rename_i hne
    exact H _ _ hn hs hdrop harr he₀ hinv
      (by rw [harity, Expr.lambdaArity_eq_zero hne]; rfl) he

/-- `lambdaTelescope` opens every leading lambda of `e` as a probe variable and hands the body,
instantiated at them, to `k`. The array of variables is consumed in reverse (`instantiateRev` is
`instantiateList` at the reversed list), and each binder is opened with `TrExprS.inst_fvar`,
which turns the `none`-tagged `vlam` the `lam` rule produces into the `withLocalDecl`
variable's.

The invariant is `inferLambda.loop.WF`'s, not just the body's translation: `m'` extends `m` by
the `n` binders opened, `fvs` are exactly those binders' variables, and `e` is the body
re-abstracted over them. A caller needs all three -- the variables to build applications at
them, and the re-abstraction because `unfoldNatWellFounded` returns
`lctx.mkLambda fvs a₀` and has to say what that is.

`lambdaTelescope.Inv` adds the translation side, which is what a caller that closes the
telescope off again needs: the domains, the lift over them, and the variables' translations. -/
theorem lambdaTelescope.WF {c : VContext} {α} {k : Array Expr → Expr → M α}
    {Q : α → VState → Prop} {m : MLCtx} [c.MLCWF m] {s : VState} {e : Expr} {e' : VExpr}
    (he : (c.withMLC m).TrExprS e e')
    (H : ∀ (fvs : Array Expr) {m'} [c.MLCWF m'] {s' body} body' {n} (hn : n ≤ m'.length) {As},
      s ≤ s' → m'.dropN n hn = m → fvs.toList.reverse = (m'.fvarRevList n hn).map .fvar →
      e = m'.mkLambda n hn body → lambdaTelescope.Inv c m m' fvs n hn As e' body' →
      e.lambdaArity = n →
      (c.withMLC m').TrExprS body body' → (k fvs body).WF (c.withMLC m') s' Q) :
    (lambdaTelescope e k).WF (c.withMLC m) s Q :=
  lambdaTelescope.loop.WF H e #[] m s e' (n := 0) (Nat.zero_le _) (by simp) rfl (by simp) (by simp)
    (As := []) ⟨rfl, by simp, .refl, by simp, rfl⟩ .rfl he

namespace Primitive

/-- Peel one argument off an application whose head has a known `forallE` type. `app_inv` only
returns the domain up to defeq, so this is where `forallE_inv` moves the argument's typing onto
the head's recorded domain -- which is what makes the argument usable in a substitution. -/
theorem _root_.Lean4Lean.VExpr.WF.app_inv' {env : VEnv} {U Γ} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {f a A B : VExpr}
    (hf : env.HasType U Γ f (.forallE A B)) (H : VExpr.WF env U Γ (.app f a)) :
    env.HasType U Γ a A ∧ env.HasType U Γ (.app f a) (B.inst a) := by
  obtain ⟨A', B', hf', ha⟩ := H.app_inv henv.orderedStrong hΓ
  obtain ⟨⟨_, hdom⟩, -⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
  have ha' := VEnv.HasType.defeqU_r henv hΓ ⟨_, hdom.symm⟩ ha
  exact ⟨ha', hf.app ha'⟩

/-- Peeling one binder off a well formed lambda: the body, in the context the binder extends.
A telescope is peeled by iterating this, which is what the conditional builders' shapes need. -/
theorem _root_.Lean4Lean.VExpr.WF.lam_inv' {env : VEnv} (henv : env.OrderedStrong)
    (hΓ : OnCtx Γ (env.IsType U)) (H : VExpr.WF env U Γ (.lam A body)) :
    OnCtx (A :: Γ) (env.IsType U) ∧ VExpr.WF env U (A :: Γ) body :=
  let ⟨hA, _, hb⟩ := VExpr.WF.lam_inv henv hΓ H; ⟨⟨hΓ, hA⟩, _, hb⟩

/-- Beta at the term level, from well-formedness of the redex alone: the argument's type comes
back from `app_inv` only up to defeq, so `forallE_inv` is what lets it be used at the binder's
own type. Fuel recursions need this after a conditional has been evaluated to one of its
branches, which is a lambda applied to the guard's proof. -/
theorem _root_.Lean4Lean.VExpr.WF.betaU {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {A body v : VExpr}
    (H : VExpr.WF env U Γ ((VExpr.lam A body).app v)) :
    env.HasType U Γ v A ∧ env.IsDefEqU U Γ ((VExpr.lam A body).app v) (body.inst v) := by
  obtain ⟨A', B', hf, ha⟩ := H.app_inv henv.orderedStrong hΓ
  obtain ⟨⟨u, hA⟩, B0, hbody⟩ := VExpr.WF.lam_inv henv.orderedStrong hΓ ⟨_, hf⟩
  have hlam : env.HasType U Γ (.lam A body) (.forallE A B0) := .lam hA hbody
  obtain ⟨⟨_, hdom⟩, -⟩ := (hlam.uniqU henv hΓ hf).forallE_inv henv hΓ
  have ha' := VEnv.HasType.defeqU_r henv hΓ ⟨_, hdom.symm⟩ ha
  exact ⟨ha', _, .beta hbody ha'⟩

variable {c : VContext} {Δ : VLCtx}

/-! ### The branches' shared preamble

`checkDef.WF` is one proof per primitive over a common set of atoms: the `Nat`
constructors as bundles, the operators someone else's recurrence uses, the codomain bundles the
type check is compared against. They only ever mention the checking context, so they live here
rather than in the theorem -- which is what lets a branch become a theorem of its own instead of
a case of one enormous proof.

The theorem still opens with its own copies of these as local definitions. Routing its branches
through the ones here instead costs about 40s of elaboration: the local versions are stated at
`v.levelParams` and the shared ones at `c.lparams`, and every defeq check between the two forms
unfolds the context. So these are for the *extracted* branches, which will have no such local
context to disagree with. -/

/-- The definition a branch is checking, with the translations `addDefinition` established for
it. A branch needs nothing else about the definition, so this is what an extracted branch takes
in place of the enclosing theorem's whole context. -/
structure Data (v : DefinitionVal) (ci' : VDefVal) (c : VContext) where
  safe : c.safety = .safe
  lparams : c.lparams = v.levelParams
  hu : c.lparams.length = ci'.uvars
  htype : TrExprS c.venv c.lparams [] v.type ci'.type
  hvalue : TrExprS c.venv c.lparams [] v.value ci'.value
  hci : c.venv.HasType ci'.uvars [] ci'.value ci'.type

variable {v : DefinitionVal} {ci' : VDefVal}

/-- A primitive named in the environment the checker ran in is present in the model. -/
theorem Data.contains (P : Data v ci' c) {n : Name} (hp : Environment.primitives.contains n)
    (h : c.env.contains n) : c.venv.contains n :=
  VContext.contains_primitive P.safe h hp

/-- `Nat.zero` and `Nat.succ`, and the two numerals spelled as constructor applications rather
than literals -- which is how the checker writes them. -/
def zerob (h : c.venv.contains ``Nat) :
    TrTerm c.venv c.lparams Δ q(Nat.zero) .nat := .natZero c.hasPrimitives h

def succb (h : c.venv.contains ``Nat) :
    TrTerm c.venv c.lparams Δ .natSucc vexpr(Nat → Nat) := .natSucc c.hasPrimitives h

def oneb (h : c.venv.contains ``Nat) :
    TrTerm c.venv c.lparams Δ (Lean.mkApp .natSucc q(Nat.zero)) .nat :=
  .natUnApp (succb h) (zerob h)

def twob (h : c.venv.contains ``Nat) :
    TrTerm c.venv c.lparams Δ (Lean.mkApp .natSucc (Lean.mkApp .natSucc q(Nat.zero))) .nat :=
  .natUnApp (succb h) (oneb h)

def boolb (h : c.venv.contains ``Bool) (b : Bool) :
    TrTerm c.venv c.lparams Δ (Lean.toExpr b) .bool := .boolLit c.hasPrimitives h b

/-- `Nat` as a type bundle at whatever depth the caller is at, and the `IsType` behind it. -/
theorem hNatT (h : c.venv.contains ``Nat) {{Δ : VLCtx}}
    (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length)) :
    c.venv.IsType c.lparams.length Δ.toCtx VExpr.nat :=
  c.hasPrimitives.natIsType c.Ewf.orderedStrong h hΔ

def trNat (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length))
    (h : c.venv.contains ``Nat) : TrTy c.venv c.lparams Δ q(Nat) :=
  .of (c.hasPrimitives.trNat c.Ewf.orderedStrong h) (hNatT h hΔ)

/-- The primitives that appear as *operators* in someone else's recurrence: `Nat.pred` in
`Nat.sub`'s, `Nat.add` in `Nat.mul`'s, and so on. Their typings come from the reflection
`HasPrimitives` records, since they are not constructors. -/
def predb (h : c.venv.contains ``Nat.pred) :
    TrTerm c.venv c.lparams Δ q(Nat.pred) vexpr(Nat → Nat) :=
  .ofConst c.Ewf.orderedStrong (c.hasPrimitives.natPred h).1

def addb (h : c.venv.contains ``Nat.add) :
    TrTerm c.venv c.lparams Δ q(Nat.add) vexpr(Nat → Nat → Nat) :=
  .ofConst c.Ewf.orderedStrong (c.hasPrimitives.natAdd h).1

def divb (h : c.venv.contains ``Nat.div) :
    TrTerm c.venv c.lparams Δ q(Nat.div) vexpr(Nat → Nat → Nat) :=
  .ofConst c.Ewf.orderedStrong (c.hasPrimitives.natDiv h).1

def modb (h : c.venv.contains ``Nat.mod) :
    TrTerm c.venv c.lparams Δ q(Nat.mod) vexpr(Nat → Nat → Nat) :=
  .ofConst c.Ewf.orderedStrong (c.hasPrimitives.natMod h).1

def mulb (h : c.venv.contains ``Nat.mul) :
    TrTerm c.venv c.lparams Δ q(Nat.mul) vexpr(Nat → Nat → Nat) :=
  .ofConst c.Ewf.orderedStrong (c.hasPrimitives.natMul h).1

/-- The codomain bundles, at the depth an arrow's body sits: two binders for the binary
primitives, one for `Nat.pred`. -/
def natCod (h : c.venv.contains ``Nat) :
    TrTy c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)] q(Nat) :=
  .of (c.hasPrimitives.trNat c.Ewf.orderedStrong h)
    (have := ⟨trivial, hNatT h trivial⟩; hNatT h ⟨this, hNatT h this⟩)

def natCod1 (h : c.venv.contains ``Nat) :
    TrTy c.venv c.lparams [(none, .vlam .nat)] q(Nat) :=
  .of (c.hasPrimitives.trNat c.Ewf.orderedStrong h) (hNatT h ⟨trivial, hNatT h trivial⟩)

def boolCod (h : c.venv.contains ``Nat) (hb : c.venv.contains ``Bool) :
    TrTy c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)] q(Bool) :=
  .of (c.hasPrimitives.trBool c.Ewf.orderedStrong hb)
    (have := ⟨trivial, hNatT h trivial⟩;
      c.hasPrimitives.boolIsType c.Ewf.orderedStrong hb ⟨this, hNatT h this⟩)

/-- `Bool` as a type bundle, the counterpart of `trNat`. -/
def trBool (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length))
    (hb : c.venv.contains ``Bool) : TrTy c.venv c.lparams Δ q(Bool) :=
  .of (c.hasPrimitives.trBool c.Ewf.orderedStrong hb)
    (c.hasPrimitives.boolIsType c.Ewf.orderedStrong hb hΔ)

/-- `Bool → Bool → Bool`, the type of `Nat.bitwise`'s operator argument. -/
def boolOp2Ty (hb : c.venv.contains ``Bool) :
    TrTy c.venv c.lparams [] q(Bool → Bool → Bool) :=
  let B0 : TrTy c.venv c.lparams [] q(Bool) := trBool (Δ := []) trivial hb
  let B1 : TrTy c.venv c.lparams [(none, .vlam .bool)] q(Bool) :=
    trBool ⟨trivial, B0.isType⟩ hb
  let B2 : TrTy c.venv c.lparams [(none, .vlam .bool), (none, .vlam .bool)] q(Bool) :=
    trBool ⟨⟨trivial, B0.isType⟩, B1.isType⟩ hb
  let OP := TrTy.forallE B0 (.forallE B1 B2)
  -- named rather than left as `OP` so that the target is `boolOp2` on the nose: the operator's
  -- own typing is read off the binder, and every consumer wants it in that form
  ⟨VExpr.boolOp2, OP.trS, OP.isType⟩

@[simp] theorem boolOp2Ty_tgt (hb : c.venv.contains ``Bool) :
    (boolOp2Ty hb).tgt = VExpr.boolOp2 := rfl

/-- `Nat.bitwise`'s type. It is the one primitive whose type is not an arrow of `Nat`s: the
operator it folds is an argument, which is exactly why its spec has to speak about every operator
a later environment might supply. -/
def bitwiseTy (hnat : c.venv.contains ``Nat) (hb : c.venv.contains ``Bool) :
    TrTy c.venv c.lparams [] q((Bool → Bool → Bool) → Nat → Nat → Nat) :=
  let B0 : TrTy c.venv c.lparams [] q(Bool) := trBool (Δ := []) trivial hb
  let B1 : TrTy c.venv c.lparams [(none, .vlam .bool)] q(Bool) :=
    trBool ⟨trivial, B0.isType⟩ hb
  let B2 : TrTy c.venv c.lparams [(none, .vlam .bool), (none, .vlam .bool)] q(Bool) :=
    trBool ⟨⟨trivial, B0.isType⟩, B1.isType⟩ hb
  let OP : TrTy c.venv c.lparams [] q(Bool → Bool → Bool) := .forallE B0 (.forallE B1 B2)
  let N0 : TrTy c.venv c.lparams [(none, .vlam .boolOp2)] q(Nat) :=
    trNat ⟨trivial, OP.isType⟩ hnat
  let N1 : TrTy c.venv c.lparams [(none, .vlam .nat), (none, .vlam .boolOp2)] q(Nat) :=
    trNat ⟨⟨trivial, OP.isType⟩, N0.isType⟩ hnat
  let N2 : TrTy c.venv c.lparams
      [(none, .vlam .nat), (none, .vlam .nat), (none, .vlam .boolOp2)] q(Nat) :=
    trNat ⟨⟨⟨trivial, OP.isType⟩, N0.isType⟩, N1.isType⟩ hnat
  .forallE OP (.forallE N0 (.forallE N1 N2))

/-- The checked type pins `ci'.type` for `Nat.bitwise`, as `mkTyEq` does for the arrows. -/
theorem Data.mkTyEqBitwise (P : Data v ci' c) (hnat : c.venv.contains ``Nat)
    (hb : c.venv.contains ``Bool)
    (h2 : v.type == q((Bool → Bool → Bool) → Nat → Nat → Nat)) :
    ci'.type = .forallE .boolOp2 .natOp2 :=
  (P.htype.eqv h2).unique (by simp [TrExprS.IsUnique]) (bitwiseTy hnat hb).trS

/-- The definition's value as a bundle, at whatever local context the probes have built up. -/
def Data.hv (P : Data v ci' c) {T} (eq : ci'.type = T) (m : MLCtx) [cwf : c.MLCWF m] :
    TrTerm c.venv c.lparams m.vlctx v.value T :=
  TrTerm.of_nil' c.Ewf m.noBV cwf.wf.tr.wf P.hvalue (P.hu ▸ eq ▸ P.hci)

/-- The checked type pins `ci'.type`: `TrExprS.eqv` moves the translation onto the shape the
checker compared against, and `unique` quotes determinism against the arrow `natArrow2` builds.
Generic in the codomain, so `Nat.beq`/`Nat.ble` pass a `Bool` bundle instead. -/
theorem Data.mkTyEq (P : Data v ci' c) (hnat : c.venv.contains ``Nat) {codSrc : Expr}
    (hcodU : TrExprS.IsUnique codSrc)
    (hcod : TrTy c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)] codSrc)
    {n₁ n₂ : Name} {d₁ d₂ : MData} {bi₁ bi₂ : BinderInfo}
    (h2 : v.type == Expr.forallE n₁ (.mdata d₁ q(Nat))
      (.forallE n₂ (.mdata d₂ q(Nat)) codSrc bi₂) bi₁) :
    ci'.type = .forallE .nat (.forallE .nat hcod.tgt) :=
  (P.htype.eqv h2).unique (by simp [TrExprS.IsUnique, hcodU])
    (.natArrow2 c.Ewf.orderedStrong c.hasPrimitives hnat hcod)

/-- The unary version, for `Nat.pred`. -/
theorem Data.mkTyEq1 (P : Data v ci' c) (hnat : c.venv.contains ``Nat) {codSrc : Expr}
    (hcodU : TrExprS.IsUnique codSrc)
    (hcod : TrTy c.venv c.lparams [(none, .vlam .nat)] codSrc)
    {n₁ : Name} {d₁ : MData} {bi₁ : BinderInfo}
    (h2 : v.type == Expr.forallE n₁ (.mdata d₁ q(Nat)) codSrc bi₁) :
    ci'.type = .forallE .nat hcod.tgt :=
  (P.htype.eqv h2).unique (by simp [TrExprS.IsUnique, hcodU])
    (.natArrow1 c.Ewf.orderedStrong c.hasPrimitives hnat hcod)

theorem Data.uvars_eq (P : Data v ci' c) (hok' : v.safety = .safe ∧ v.levelParams = []) :
    ci'.uvars = 0 := by rw [← P.hu, P.lparams, hok'.2]; rfl

/-- What the primitive-definition recognizer must establish beyond ordinary type checking.
This is kept separate from declaration checking so that the remaining metatheory does not
depend on the recognizer's syntactic implementation. Primitive semantics are claimed only
in well-formed extensions of the environment in which recognition ran. -/
structure PrimitiveResult (checked : VEnv) (v : DefinitionVal) (ci' : VDefVal) : Prop where
  safe : v.safety = .safe
  no_level_params : v.levelParams = []
  preserves : ∀ {safety : DefinitionSafety} {venv env' : VEnv},
    checked ≤ venv → venv.WF → venv.HasPrimitives →
    TrDefVal safety venv (.defnInfo v) ci' → ci'.WF venv →
    venv.addConst v.name ci'.toVConstant = some env' →
    (env'.addDefEq ci'.toDefEq).HasPrimitives

/-- What every `ReflectsNatNatNat` branch has to produce, once the guards have fired: its spec's
entry, the type it checked, and the reflection of the *value* in the checked environment.
`preserves`' quantification over extensions is discharged here, so a branch never sees it. -/
theorem Data.mkResult (P : Data v ci' c) {F} (hok' : v.safety = .safe ∧ v.levelParams = [])
    (hnat : c.venv.contains ``Nat)
    (hmem : (v.name, .reflectsNatNatNat F) ∈ primSpecs)
    (tyeq : ci'.type = vexpr(Nat → Nat → Nat))
    (href : c.venv.HasType c.lparams.length [] ci'.value vexpr(Nat → Nat → Nat) →
      c.venv.ReflectsNatNatNat' ci'.value F) :
    PrimitiveResult c.venv v ci' := by
  refine ⟨hok'.1, hok'.2, fun hle hwf hprim htr hciv hadd => ?_⟩
  have hnm : v.name = ci'.name := htr.1.2
  have huv := P.uvars_eq hok'
  exact hprim.addPrimitiveDefEq hadd (s₀ := .reflectsNatNatNat F) (hnm ▸ hmem) fun _ =>
    hnm ▸ VEnv.ReflectsNatNatNat'.toConst hle c.Ewf hwf c.hasPrimitives hnat huv hciv
      (hnm ▸ hadd) (href (P.hu ▸ tyeq ▸ P.hci))

theorem Data.mkResult1 (P : Data v ci' c) {F} (hok' : v.safety = .safe ∧ v.levelParams = [])
    (hnat : c.venv.contains ``Nat)
    (hmem : (v.name, .reflectsNatNat F) ∈ primSpecs)
    (tyeq : ci'.type = vexpr(Nat → Nat))
    (href : c.venv.HasType c.lparams.length [] ci'.value vexpr(Nat → Nat) →
      c.venv.ReflectsNatNat' ci'.value F) :
    PrimitiveResult c.venv v ci' := by
  refine ⟨hok'.1, hok'.2, fun hle hwf hprim htr hciv hadd => ?_⟩
  have hnm : v.name = ci'.name := htr.1.2
  have huv := P.uvars_eq hok'
  exact hprim.addPrimitiveDefEq hadd (s₀ := .reflectsNatNat F) (hnm ▸ hmem) fun _ =>
    hnm ▸ VEnv.ReflectsNatNat'.toConst hle c.Ewf hwf c.hasPrimitives hnat huv hciv
      (hnm ▸ hadd) (href (P.hu ▸ tyeq ▸ P.hci))

theorem Data.mkResultBool (P : Data v ci' c) {F} (hok' : v.safety = .safe ∧ v.levelParams = [])
    (hnat : c.venv.contains ``Nat)
    (hmem : (v.name, .reflectsNatNatBool F) ∈ primSpecs)
    (tyeq : ci'.type = vexpr(Nat → Nat → Bool))
    (href : c.venv.HasType c.lparams.length [] ci'.value vexpr(Nat → Nat → Bool) →
      c.venv.ReflectsNatNatBool' ci'.value F) :
    PrimitiveResult c.venv v ci' := by
  refine ⟨hok'.1, hok'.2, fun hle hwf hprim htr hciv hadd => ?_⟩
  have hnm : v.name = ci'.name := htr.1.2
  have huv := P.uvars_eq hok'
  exact hprim.addPrimitiveDefEq hadd (s₀ := .reflectsNatNatBool F) (hnm ▸ hmem) fun _ =>
    hnm ▸ VEnv.ReflectsNatNatBool'.toConst hle c.Ewf hwf c.hasPrimitives hnat huv hciv
      (hnm ▸ hadd) (href (P.hu ▸ tyeq ▸ P.hci))

/-- `Nat.bitwise`'s obligation: the recorded type, and the reflection at *every* operator that any
well-formed extension might supply. The second half is what forced the recognizer's ground layer
to be read in an extension rather than in `c.venv`; here it is handed on unchanged, with the
constant swapped for the value by the equation `addDefEq` adds. -/
theorem Data.mkResultBitwise (P : Data v ci' c) (hok' : v.safety = .safe ∧ v.levelParams = [])
    (hnat : c.venv.contains ``Nat)
    (hmem : (v.name, PrimSpec.reflectsBitwise) ∈ primSpecs)
    (tyeq : ci'.type = .forallE .boolOp2 .natOp2)
    (href : ∀ env' : VEnv, c.venv ≤ env' → env'.WF →
      ∀ f g, env'.ReflectsBoolBoolBool' f g →
        env'.ReflectsNatNatNat' (ci'.value.app f) (Nat.bitwise g)) :
    PrimitiveResult c.venv v ci' := by
  refine ⟨hok'.1, hok'.2, fun hle hwf hprim htr hciv hadd => ?_⟩
  rw [show v.name = ci'.name from htr.1.2] at hadd hmem
  have huv := P.uvars_eq hok'
  obtain ⟨hwfE, hcf⟩ := VDefVal.addDefEq_wf hwf huv hciv hadd
  have hleE := (VEnv.addConst_le hadd).trans (VEnv.addDefEq_le (df := ci'.toDefEq))
  refine hprim.addPrimitiveDefEq hadd (s₀ := .reflectsBitwise) hmem fun _ => ⟨fun ci hci => ?_, ?_⟩
  · simp [VEnv.addDefEq] at hci; rw [VEnv.addConst_self hadd] at hci; cases hci
    rw [← huv, ← tyeq]
  intro env'' hle'' hwf'' f g hfg
  -- the value reflects at this operator, by the caller's own argument
  have hr := href env'' (hle.trans (hleE.trans hle'')) hwf'' f g hfg
  have hvT : env''.HasType 0 [] ci'.value (.forallE .boolOp2 .natOp2) := by
    rw [← tyeq, ← huv]; exact hciv.mono (hleE.trans hle'')
  -- the constant is the value there, so the reflection moves onto it
  have hcf' := hcf.mono hle''
  have hcT := hvT.defeqU_l hwf'' trivial hcf'.symm
  refine VEnv.ReflectsNatNatNat'.congr_head hwf'' (fun k Γ => ?_) hr
    (hcf'.app_fun' hwf'' trivial hcT hfg.1) ?_
  · exact (c.hasPrimitives.natLitT c.Ewf.orderedStrong hnat k Γ).mono (hle.trans (hleE.trans hle''))
  · simpa [VExpr.natOp2, VExpr.nat, VExpr.inst] using VEnv.HasType.app hcT hfg.1

/-- `Char.ofNat` records only its type, so its whole obligation is `ci'`'s recorded constant. -/
theorem Data.mkResultTypeEq (P : Data v ci' c) {T} (hok' : v.safety = .safe ∧ v.levelParams = [])
    (hmem : (v.name, .typeEq T) ∈ primSpecs) (tyeq : ci'.type = T) :
    PrimitiveResult c.venv v ci' := by
  refine ⟨hok'.1, hok'.2, fun hle hwf hprim htr hciv hadd => ?_⟩
  have hnm : v.name = ci'.name := htr.1.2
  have huv := P.uvars_eq hok'
  refine hprim.addPrimitiveDefEq hadd (s₀ := .typeEq T) (hnm ▸ hmem) fun ci hci => ?_
  have := VEnv.addConst_self hadd
  simp [VEnv.addDefEq] at hci; rw [this] at hci; cases hci
  rw [← huv, ← tyeq]

/-! #### Fuel recursions

`Nat.div` and `Nat.mod` are the same recursion: a `go` taking a bound, a proof that it is
positive, a fuel, the argument and a proof that the fuel covers it. Everything about it that does
not mention the checker lives here, so that a branch only has to produce its own equation. -/

/-- A call of `Nat.div.go` or `Nat.modCore.go`, whose checked type is
`∀ y, 1 ≤ y → ∀ fuel x, succ x ≤ fuel → Nat` for whatever `≤` the branch checked. That type is
spelled out at each use rather than named: naming it means unfolding it inside the peeling
simps below, which is measurably slower. -/
def natGoCall (go' bb pf f x pf' : VExpr) : VExpr := ((((go'.app bb).app pf).app f).app x).app pf'

/-- The type the fuel recursion's `go` is checked against: the divisor and its positivity, then
the fuel, the dividend and the bound that makes the recursion terminate. -/
abbrev natGoType (le' : VExpr) : VExpr :=
  .forallE .nat <| .forallE ((le'.app (.natLit 1)).app (.bvar 0)) <|
  .forallE .nat <| .forallE .nat <|
    .forallE ((le'.app (.app .natSucc (.bvar 0))).app (.bvar 1)) .nat

/-- What `go`'s recorded type says about the arguments of a well formed call. `app_inv` alone
gives them types only up to defeq, so each is moved onto the recorded domain in turn -- which is
what makes them usable in a substitution, and what types the call itself. -/
theorem goArgs {c : VContext} {go' le' : VExpr}
    (hgoT : ∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ go' (natGoType le'))
    (hleC : le'.ClosedN) {bb pf f x pf' : VExpr}
    (hwf : c.WF₀ (natGoCall go' bb pf f x pf')) :
    c.HasType₀ bb .nat ∧ c.HasType₀ pf ((le'.app (.natLit 1)).app bb) ∧
    c.HasType₀ f .nat ∧ c.HasType₀ x .nat ∧
    c.HasType₀ pf' ((le'.app (VExpr.natSucc.app x)).app f) ∧
    c.HasType₀ (natGoCall go' bb pf f x pf') .nat := by
  simp only [natGoCall] at hwf ⊢
  obtain ⟨_, _, h4, -⟩ := hwf.app_inv c.Ewf.orderedStrong trivial
  obtain ⟨_, _, h3, -⟩ := VExpr.WF.app_inv c.Ewf.orderedStrong trivial ⟨_, h4⟩
  obtain ⟨_, _, h2, -⟩ := VExpr.WF.app_inv c.Ewf.orderedStrong trivial ⟨_, h3⟩
  obtain ⟨_, _, h1, -⟩ := VExpr.WF.app_inv c.Ewf.orderedStrong trivial ⟨_, h2⟩
  obtain ⟨hbbT, k1⟩ := VExpr.WF.app_inv' c.Ewf trivial (hgoT (Γ := [])) ⟨_, h1⟩
  simp [VExpr.inst, VExpr.instVar, VExpr.natLit, VExpr.natSucc, VExpr.natZero,
    VExpr.nat, VExpr.liftN_zero,
    hleC.instN_eq (Nat.zero_le _)] at k1
  obtain ⟨hpfT, k2⟩ := VExpr.WF.app_inv' c.Ewf trivial k1 ⟨_, h2⟩
  simp [VExpr.inst, VExpr.instVar, hleC.instN_eq (Nat.zero_le _)] at k2
  obtain ⟨hfT, k3⟩ := VExpr.WF.app_inv' c.Ewf trivial k2 ⟨_, h3⟩
  simp [VExpr.inst, VExpr.instVar, hleC.instN_eq (Nat.zero_le _)] at k3
  obtain ⟨hxT, k4⟩ := VExpr.WF.app_inv' c.Ewf trivial k3 ⟨_, h4⟩
  simp [VExpr.inst, VExpr.instVar, VExpr.liftN_zero, VExpr.inst_lift,
    hleC.instN_eq (Nat.zero_le _)] at k4
  obtain ⟨hpf'T, hcallT⟩ := VExpr.WF.app_inv' c.Ewf trivial k4 hwf
  simp [VExpr.inst] at hcallT
  exact ⟨hbbT, hpfT, hfT, hxT, hpf'T, hcallT⟩

/-- The fuel recursion runs to the end: at literals, a well formed call returns `F x bb`.

`Nat.div` and `Nat.mod` differ only in what the step does to the recursive call -- `Nat.succ` for
`div`, nothing for `mod` -- and in what the recursion returns when it stops, so both are this
lemma. `hstep` is the branch's own equation, already closed at literals and evaluated; everything
above it (the conditional, the beta, the `Nat.sub` reflection) is the branch's business, and
everything below it -- the induction, and that the arithmetic matches -- is this. -/
theorem natFuelRec {c : VContext} {go' le' : VExpr} {F : Nat → Nat → Nat} {h : Nat → Nat}
    {H : VExpr → VExpr} {E : Nat → Nat}
    (hgoT : ∀ {Γ : List VExpr}, c.venv.HasType c.lparams.length Γ go' (natGoType le'))
    (hleC : le'.ClosedN)
    (hFlt : ∀ bb x, x < bb → F x bb = E x)
    (hFstep : ∀ bb x, 0 < bb → bb ≤ x → F x bb = h (F (x - bb) bb))
    (hHwf : ∀ {e}, c.WF₀ (H e) → c.WF₀ e)
    (hH : ∀ {e n}, c.HasType₀ e .nat → c.IsDefEqU₀ e (.natLit n) →
      c.IsDefEqU₀ (H e) (.natLit (h n)))
    (hstep : ∀ (bb x f' : Nat) (pf pf' : VExpr), 0 < bb →
      c.WF₀ (natGoCall go' (.natLit bb) pf (.natLit (f'+1)) (.natLit x) pf') →
      if bb ≤ x then
        ∃ pf3, c.IsDefEqU₀ (natGoCall go' (.natLit bb) pf (.natLit (f'+1)) (.natLit x) pf')
          (H (natGoCall go' (.natLit bb) pf (.natLit f') (.natLit (x - bb)) pf3))
      else c.IsDefEqU₀ (natGoCall go' (.natLit bb) pf (.natLit (f'+1)) (.natLit x) pf')
        (.natLit (E x)))
    (f bb x : Nat) (pf pf' : VExpr) (hbb : 0 < bb) (hlt : x < f)
    (hwf : natGoCall go' (.natLit bb) pf (.natLit f) (.natLit x) pf'
      |>.WF c.venv c.lparams.length []) :
    c.IsDefEqU₀ (natGoCall go' (.natLit bb) pf (.natLit f) (.natLit x) pf')
      (.natLit (F x bb)) := by
  induction f generalizing x pf' with | zero => cases Nat.not_lt_zero _ hlt | succ f' ih
  specialize hstep bb x f' pf pf' hbb hwf
  split at hstep <;> rename_i h <;> [skip; exact hFlt bb x (Nat.lt_of_not_le h) ▸ hstep]
  -- the recursion steps, at `x - bb` and one less fuel
  obtain ⟨pf3, heq⟩ := hstep
  have hwf3 := hHwf ⟨_, VEnv.HasType.defeqU_l c.Ewf trivial heq hwf.choose_spec⟩
  refine heq.trans c.Ewf trivial <| hFstep bb x hbb h ▸ ?_
  exact hH (goArgs hgoT hleC hwf3).2.2.2.2.2 (ih (x - bb) pf3 (by omega) hwf3)

/-- The shape every guard in the checker has: a test that throws on failure and carries on
otherwise, so a `fail` in front of a continuation proves whatever the continuation was to. -/
theorem elseFail {α : Type} {p : Prop} [Decidable p] {c s f Q} {e : Exception}
    (H : p → M.WF (α := α) c s f Q) :
    (if p then f else do let _ : Unit ← throw e; f).WF c s Q := by
  split <;> [exact H ‹_›; exact .bindThrow .throw]

/-- The recognizer only ever runs on a safe definition with no universe parameters. -/
theorem hok {v : DefinitionVal} (h : ok v) : v.safety = .safe ∧ v.levelParams = [] := by
  simp_all [ok]
