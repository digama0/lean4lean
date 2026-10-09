import Batteries.Data.String.Lemmas
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Verify.Typing.PrimSpec
import Lean4Lean.Verify.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ConstructorCaptureTransport
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Instantiate

/-!
# Syntactic infrastructure: scoping and context relations

The facts about source expressions and translation contexts that the translation relations
(`TrSyn`, `TrExprS`) are transported along, with no translation in sight:

* scoping of kernel expressions: `Closed` (bound variables) and `FVarsIn` (free variables),
  through abstraction, instantiation and literal encodings;
* the context relations `VLCtx.FVLift'`, `VLCtx.FVLift` (free-variable weakening),
  `VLCtx.BVLift` (bound-variable weakening), `VLCtx.InstN`, `VLCtx.InstLet` (substitution) and
  `VLCtx.Abstract` (abstraction of a free variable), with their effect on lookups (`find?`);
  the lookup lemmas need at most distinct free variables, not a well-formed context;
* `TrExprS.IsUniqueCtx`: contexts that differ only in their binder domains, in which lookups
  agree on values.

The well-formedness lemmas for the same relations (`VLCtx.InstN.wf`, ...) are here too, since they
are stated along the relations.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean
open scoped _root_.List

theorem OnCtx.levelWF_of_isType {env : VEnv} {U : Nat} {Γ : List VExpr}
    (H : OnCtx Γ (env.IsType U)) : OnCtx Γ (fun _ A => A.LevelWF U) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih => exact ⟨ih H.1, (Classical.choose_spec H.2).levelWF (ih H.1) |>.1⟩

theorem fvarsIn_iff : FVarsIn P e ↔ (∀ fv ∈ e.fvarsList, P fv) ∧ FVarsIn (fun _ => True) e := by
  induction e <;> simp [FVarsIn, Expr.fvarsList, *] <;> grind

theorem fvarsIn_iff_hasMVar : FVarsIn (fun _ => True) e ↔ e.hasMVar = false := by
  rw [Expr.hasMVar, ← Expr.hasExprMVar, ← Expr.hasLevelMVar]; simp
  induction e <;> simp [FVarsIn, Expr.hasExprMVar', Expr.hasLevelMVar', and_assoc, and_left_comm, *]

theorem fvarsList_eq_nil {e : Expr} : e.fvarsList = [] ↔ e.hasFVar = false := by
  rw [Expr.hasFVar_eq]
  induction e <;> simp [Expr.fvarsList, Expr.hasFVar', and_assoc, *]

theorem FVarsIn.mp (H : ∀ fv, P fv → Q fv → R fv) :
    ∀ {e}, FVarsIn P e → FVarsIn Q e → FVarsIn R e
  | .bvar _, l, _ | .sort .., l, _ | .const .., l, _ | .lit .., l, _ => l
  | .fvar _, l, r => H _ l r
  | .app .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .lam .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .forallE .., ⟨l1, l2⟩, ⟨r1, r2⟩ => ⟨l1.mp H r1, l2.mp H r2⟩
  | .letE .., ⟨l1, l2, l3⟩, ⟨r1, r2, r3⟩ => ⟨l1.mp H r1, l2.mp H r2, l3.mp H r3⟩
  | .proj _ _ e, l, r | .mdata _ e, l, r => l.mp (e := e) H r

theorem FVarsIn.mono (H : ∀ fv, P fv → Q fv) (h : FVarsIn P e) : FVarsIn Q e :=
  h.mp (fun _ h _ => H _ h) h

theorem Closed.mono (H : k ≤ k') : ∀ {e}, Closed e k → Closed e k'
  | .bvar _, h => Nat.lt_of_lt_of_le h H
  | .fvar _, h | .sort .., h | .const .., h | .lit .., h => h
  | .app .., ⟨h1, h2⟩ => ⟨h1.mono H, h2.mono H⟩
  | .lam .., ⟨h1, h2⟩
  | .forallE .., ⟨h1, h2⟩ => ⟨h1.mono H, h2.mono (Nat.succ_le_succ H)⟩
  | .letE .., ⟨h1, h2, h3⟩ => ⟨h1.mono H, h2.mono H, h3.mono (Nat.succ_le_succ H)⟩
  | .proj _ _ e, h | .mdata _ e, h => h.mono (e := e) H

theorem FVarsIn.natLitToConstructor : FVarsIn P (.natLitToConstructor n) := by
  cases n <;> simp [FVarsIn, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem Closed.natLitToConstructor : Closed (.natLitToConstructor n) k := by
  cases n <;> simp [Closed, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem FVarsIn.strLitToConstructor : FVarsIn P (.strLitToConstructor s) := by
  simp [FVarsIn, Expr.strLitToConstructor]
  induction s.toList <;> simp [*, FVarsIn, Level.hasMVar']

theorem Closed.strLitToConstructor : Closed (.strLitToConstructor s) k := by
  simp [Closed, Expr.strLitToConstructor]
  induction s.toList <;> simp [*, Closed]

theorem FVarsIn.toConstructor : ∀ {l : Literal}, FVarsIn P l.toConstructor
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem FVarsIn.litType {l : Literal} : FVarsIn P l.type := by
  cases l <;> simp [FVarsIn, Literal.type]

theorem Closed.toConstructor : ∀ {l : Literal}, Closed l.toConstructor k
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem Closed.litType {l : Literal} : Closed l.type k := by cases l <;> trivial

theorem FVarsIn.fvars_cons :
    FVarsIn (· ∈ VLCtx.fvars Δ) e → FVarsIn (· ∈ VLCtx.fvars ((ofv, d) :: Δ)) e :=
  FVarsIn.mono fun a h => by cases ofv <;> simp [h]

theorem FVarsIn.default {P} : FVarsIn P (default : Expr) := by
  show FVarsIn P (Expr.const _ []); exact nofun

/-- Digging into an application spine keeps the free variables in the context. `getRevArg!`
panics off the spine, and the panic value is a constant, so that case is vacuous too. -/
theorem FVarsIn.getRevArg! {P} : ∀ {e : Expr} {i}, FVarsIn P e → FVarsIn P (e.getRevArg! i)
  | .app _ a, 0, h => h.2
  | .app f _, i+1, h => h.1.getRevArg! (i := i)
  | .bvar .., _, _ | .fvar .., _, _ | .mvar .., _, _ | .sort .., _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit .., _, _
  | .mdata .., _, _ | .proj .., _, _ => by
    simpa [Expr.getRevArg!] using FVarsIn.default

theorem FVarsIn.getArg! {P} {e : Expr} {i n} (h : FVarsIn P e) :
    FVarsIn P (e.getArg! i n) := h.getRevArg!
theorem FVarsIn.abstract_instantiate1 (h : FVarsIn (· ≠ v) e) :
    (Expr.instantiate1' e (.fvar v) k).abstract1 v k = e := by
  induction e generalizing k with simp_all [Expr.instantiate1', Expr.abstract1, FVarsIn]
  | bvar i =>
    split <;> [skip; split]
    · simp [Expr.abstract1, *]
    · simp [Expr.abstract1, Expr.liftLooseBVars', *]
    · obtain _|i := i <;> simp [Expr.abstract1] <;> omega
  | fvar v' => exact Ne.symm h

theorem FVarsIn.abstract_eq_self (h : FVarsIn (· ≠ v) e) (hc : Closed e k) :
    e.abstract1 v k = e := by
  induction e generalizing k <;> simp_all [FVarsIn, Closed, Expr.abstract1]
  exact Ne.symm h

/-- The converse of `FVarsIn.abstract_eq_self`. `Expr.abstract1_eq_self` already says an
abstraction that left no loose bvar behind did nothing; this says the same thing about the
variable rather than the term, which is the form a context argument wants.

The incoming `FVarsIn P e` is not redundant: `FVarsIn` also demands mvar-freeness of levels and
is outright `False` on `.mvar`, and no loose-bvar fact can supply that. It always comes from the
term's own translation, which is where mvar-freeness lives. -/
theorem FVarsIn.of_abstract1 {v : FVarId} {e : Expr} {k}
    (hP : FVarsIn P e) (h : (Expr.abstract1 v e k).looseBVarRange' ≤ k) :
    FVarsIn (fun fv => P fv ∧ fv ≠ v) e := by
  induction e generalizing k with
  | fvar v' =>
    simp only [Expr.abstract1] at h
    split at h
    · simp only [Expr.looseBVarRange'] at h; omega
    · rename_i hne; exact ⟨hP, fun eq => hne (by simp [eq])⟩
  | _ => simp_all [FVarsIn, Expr.abstract1, Expr.looseBVarRange', Nat.max_le] <;> grind

theorem FVarsIn.of_abstractList {vs : List FVarId} : ∀ {e : Expr} {k},
    FVarsIn P e → (Expr.abstractList e vs k).looseBVarRange' ≤ k →
    FVarsIn (fun fv => P fv ∧ fv ∉ vs) e := by
  induction vs with
  | nil => exact fun hP _ => hP.mono fun _ h => ⟨h, by simp⟩
  | cons a vs ih =>
    intro e k hP h
    have h1 : (Expr.abstractList (Expr.abstract1 a e k) vs k).looseBVarRange' ≤ k := h
    have hA : (Expr.abstract1 a e k).looseBVarRange' ≤ k := Expr.abstractList_eq_self h1 ▸ h1
    have he : Expr.abstract1 a e k = e := Expr.abstract1_eq_self hA
    exact (ih hP (he ▸ h1)).mp (fun _ x y => ⟨x.1, by simp [y.2, x.2]⟩)
      (FVarsIn.of_abstract1 hP hA)

theorem FVarsIn.liftLooseBVars (h : FVarsIn P e) : FVarsIn P (Expr.liftLooseBVars' e s d) := by
  induction e generalizing s <;> simp_all [FVarsIn, Expr.liftLooseBVars']

theorem FVarsIn.instantiate1_go (h1 : FVarsIn P e) (h2 : FVarsIn P a) :
    FVarsIn P (Expr.instantiate1' e a k) := by
  induction e generalizing k <;> simp_all [FVarsIn, Expr.instantiate1']
  (repeat' split) <;> simp [*, FVarsIn.liftLooseBVars, FVarsIn]

theorem FVarsIn.instantiate1 (h1 : FVarsIn P e) (h2 : FVarsIn P a) :
    FVarsIn P (Expr.instantiate1' e a) := h1.instantiate1_go h2

theorem FVarsIn.instantiateList (h1 : FVarsIn P e) (h2 : ∀ a ∈ as, FVarsIn P a) (k := 0) :
    FVarsIn P (Expr.instantiateList e as k) := by
  induction as generalizing e <;> simp_all [Expr.instantiateList, FVarsIn.instantiate1_go]

/-- Simultaneous abstraction cancels simultaneous instantiation by a
duplicate-free list of fresh variables.  This is stated for the transparent
list models of Lean's opaque `Expr.instantiateRev` and `Expr.abstract`
primitives, so users of those primitives can reach it through
`Expr.instantiateRev_eq` and `Expr.abstract_eq`. -/
theorem FVarsIn.abstractList_instantiateRevList
    (hfree : FVarsIn (fun v => v ∉ vars) e)
    (hnodup : vars.Nodup) :
    (e.instantiateRevList (vars.map Expr.fvar) k).abstractList vars k = e := by
  induction vars generalizing e with
  | nil => simp
  | cons v vars ih =>
    simp only [List.nodup_cons] at hnodup
    simp only [List.map_cons, Expr.instantiateRevList, Expr.abstractList]
    rw [FVarsIn.abstract_instantiate1]
    · apply ih
      · exact hfree.mono fun fv hfv hmem => hfv (by simp [hmem])
      · exact hnodup.2
    · rw [← Expr.instantiateList_reverse]
      apply FVarsIn.instantiateList
        (P := fun fv => fv ≠ v)
        (e := e) (k := k)
        (as := (vars.map Expr.fvar).reverse)
      · exact hfree.mono fun fv hfv heq => hfv (by simp [heq])
      · intro replacement hreplacement
        have hreplacement' : replacement ∈ vars.map Expr.fvar := by
          simpa using hreplacement
        rcases List.mem_map.mp hreplacement' with ⟨fv, hfv, rfl⟩
        change fv ≠ v
        exact fun heq => hnodup.1 (heq ▸ hfv)

/-- Array-facing cancellation law for Lean's abstraction and
reverse-instantiation primitives. -/
theorem FVarsIn.abstract_instantiateRev_fvarArray
    (xs : Array Expr) (vars : List FVarId)
    (hvars : xs = (vars.map Expr.fvar).toArray)
    (hfree : FVarsIn (fun v => v ∉ vars) e)
    (hnodup : vars.Nodup) (hlb : e.looseBVarRange' ≤ vars.length) :
    (e.instantiateRev xs).abstract xs = e := by
  subst xs
  rw [Expr.instantiateRev_eq, Expr.instantiate_eq, Expr.abstractN_eq]
  have hclosed : (e.instantiateList ((vars.map Expr.fvar).toArray.reverse.toList)).looseBVarRange'
      ≤ 0 := by
    have hinst : (Expr.instantiateList e ((vars.map Expr.fvar).toArray.reverse.toList) 0).looseBVarRange'
        ≤ 0 + 0 :=
      Expr.instantiateList_looseBVarRange (by simpa using hlb)
        (by intro a ha; simp at ha; obtain ⟨_, _, rfl⟩ := ha; exact Nat.le_refl 0)
    simpa using hinst
  rw [Expr.abstractN_eq_abstractList hnodup _ _ hclosed]
  simpa [Expr.instantiateList_reverse] using
    hfree.abstractList_instantiateRevList (k := 0) hnodup

/-- Reopening after the cancellation law substitutes a new parameter array
into the original abstract body. -/
theorem FVarsIn.reabstract_instantiateRev_fvarArray
    (xs ys : Array Expr) (vars : List FVarId)
    (hvars : xs = (vars.map Expr.fvar).toArray)
    (hfree : FVarsIn (fun v => v ∉ vars) e)
    (hnodup : vars.Nodup) (hlb : e.looseBVarRange' ≤ vars.length) :
    ((e.instantiateRev xs).abstract xs).instantiateRev ys =
      e.instantiateRev ys := by
  rw [hfree.abstract_instantiateRev_fvarArray xs vars hvars hnodup hlb]

theorem FVarsIn.abstract1 (h1 : FVarsIn P e) :
    FVarsIn P (Expr.abstract1 a e k) := by
  induction e generalizing k <;> simp_all [FVarsIn, Expr.abstract1]
  split <;> simp [FVarsIn, *]

theorem FVarsIn.mkAppRevList :
    FVarsIn P (f.mkAppRevList es) ↔ FVarsIn P f ∧ ∀ e ∈ es, FVarsIn P e := by
  induction es <;> simp [FVarsIn, and_comm, and_left_comm, *]

-- Used by `Lean4Lean/Verify/TypeChecker/InferType.lean`.
alias FVarsIn.appRevList := FVarsIn.mkAppRevList

theorem FVarsIn.getAppFn (h : FVarsIn P e) : FVarsIn P e.getAppFn := by
  rw [← e.mkAppRevList_getAppArgsRevList, FVarsIn.mkAppRevList] at h; exact h.1

-- Used by `Lean4Lean/Verify/TypeChecker/InferType.lean`.
alias FVarsIn.appFn := FVarsIn.getAppFn

/-- Abstracting a variable removes it from what the term mentions, so the predicate may drop it.
The companion to `FVarsIn.abstract1`, which keeps the predicate fixed; this is the form a caller
that opened a binder and is now closing it again wants. -/
theorem FVarsIn.abstract1_erase {a : FVarId} : ∀ {e : Expr} {k},
    FVarsIn (fun fv => P fv ∨ fv = a) e → FVarsIn P (Expr.abstract1 a e k) := by
  intro e
  induction e with (intro k h; simp_all [FVarsIn, Expr.abstract1])
  | fvar v => split <;> simp_all [FVarsIn]; exact h.resolve_right (Ne.symm ‹_›)

theorem Closed.abstract1 (h1 : Closed e k) :
    Closed (Expr.abstract1 a e k) (k+1) := by
  induction e generalizing k with simp_all [Closed, Expr.abstract1]
  | bvar => omega
  | fvar => split <;> simp [Closed]

theorem Closed.getAppFn {e} (h : Closed e) : Closed e.getAppFn := by
  unfold Expr.getAppFn; split
  · exact Closed.getAppFn h.1
  · exact h

theorem Closed.getAppArgsRevList {e} (h : Closed e)
    {{a}} (ha : a ∈ e.getAppArgsRevList) : Closed a := by
  revert a; unfold Expr.getAppArgsRevList; split <;> simp
  exact ⟨h.2, Closed.getAppArgsRevList h.1⟩

theorem Closed.getAppArgsList {e} (h : Closed e)
    {{a}} (ha : a ∈ e.getAppArgsList) : Closed a :=
  h.getAppArgsRevList (by simpa [← Expr.getAppArgsList_reverse])

theorem Closed.looseBVarRange_le : Closed e k → e.looseBVarRange' ≤ k := by
  induction e generalizing k <;>
    simp +contextual [*, Closed, Expr.looseBVarRange', Nat.max_le]
  exact id

theorem Closed.looseBVarRange_zero (H : Closed e) : e.looseBVarRange' = 0 := by
  simpa using H.looseBVarRange_le

/-- The converse of `Closed.looseBVarRange_le`, which is how a decidable closedness test is
cashed in. The metavariable hypothesis is not optional: `looseBVarRange'` returns `0` on
`.mvar`, while `Closed` rules metavariables out outright. -/
theorem Closed.of_looseBVarRange : ∀ {e : Expr} {k},
    e.hasExprMVar' = false → e.looseBVarRange' ≤ k → Closed e k := by
  intro e
  induction e <;> intro k hm hb <;>
    simp_all [Closed, Expr.looseBVarRange', Expr.hasExprMVar', Nat.max_le]; omega

theorem Closed.of_looseBVarRange_zero
    (hm : e.hasExprMVar' = false) (hb : e.looseBVarRange' = 0) : Closed e :=
  .of_looseBVarRange hm (Nat.le_of_eq hb)

theorem Closed.instantiate1 : ∀ {e : Expr} {k},
    Closed e (k+1) → Closed a → Closed (Expr.instantiate1' e a k) k := by
  intro e
  induction e <;> intro k he ha <;> simp_all [Closed, Expr.instantiate1']
  rename_i i
  split
  · simpa [Closed]
  · split
    · rw [Expr.liftLooseBVars_eq_self (by simpa using ha.looseBVarRange_zero)]
      exact ha.mono (Nat.zero_le _)
    · simp [Closed]; omega

/-- Exact-model form of `FVarsIn.abstract_instantiate1`: closing a fresh variable after
opening a binder with it is the identity on bodies closed below that binder. -/
theorem FVarsIn.abstractN_instantiate1 {e : Expr} {v : FVarId} {k : Nat}
    (h : FVarsIn (· ≠ v) e) (hc : Closed e (k + 1)) :
    (Expr.instantiate1' e (.fvar v) k).abstractN [v] k = e := by
  rw [Expr.abstractN_singleton (hc.instantiate1 (a := Expr.fvar v) trivial).looseBVarRange_le]
  exact h.abstract_instantiate1

/-- `FVarsIn` rules out free variables, expression metavariables *and* level metavariables --
the last in the `sort` and `const` cases -- so all three flags are needed. -/
theorem FVarsIn.of_hasFVar {P} : ∀ {e : Expr},
    e.hasFVar' = false → e.hasLevelMVar' = false → e.hasExprMVar' = false → FVarsIn P e := by
  intro e
  induction e <;> intro hf hl hm <;>
    simp_all [FVarsIn, Expr.hasFVar', Expr.hasLevelMVar', Expr.hasExprMVar']

/-- A term that does not contain a variable has its other variables' membership sharpened by
that fact: this is how a `containsFVar` guard in the checker becomes a statement about the
context a term lives in. -/
theorem FVarsIn.of_containsFVar' {P} {fv} : ∀ {e : Expr}, FVarsIn P e →
    e.containsFVar' fv = false → FVarsIn (fun y => P y ∧ y ≠ fv) e := by
  intro e; induction e <;> intro h hc <;> simp_all [FVarsIn, Expr.containsFVar']

theorem VLocalDecl.lift'_consN_skipN {d : VLocalDecl} :
    d.lift' (.consN (.skipN .refl n) k) = d.liftN n k := by
  cases d <;> simp [VLocalDecl.lift', VLocalDecl.liftN, VExpr.lift'_consN_skipN]

theorem VLocalDecl.WF.hasType : ∀ {d}, VLocalDecl.WF env U (VLCtx.toCtx Δ) d →
    env.HasType U (VLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

nonrec theorem VLocalDecl.WF.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ') :
    ∀ {d}, WF env U Γ d → WF env U Γ' (d.liftN n k)
  | .vlam _,  H | .vlet .., H => H.weakN henv W

nonrec theorem VLocalDecl.WF.instN (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) : ∀ {d}, WF env U Γ₁ d → WF env U Γ (d.inst e₀ k)
  | .vlam _,  H | .vlet .., H => H.instN henv W h₀

nonrec theorem VLocalDecl.WF.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {d}, WF env ls.length Γ d → WF env U' (Γ.map (·.instL ls)) (d.instL ls)
  | .vlam _,  H | .vlet .., H => H.instL hls

theorem VLocalDecl.is_liftN {Δ : VLCtx} :
    ∀ {d}, Ctx.LiftN (VLocalDecl.depth d) 0 Δ.toCtx (VLCtx.toCtx ((ofv, d) :: Δ))
  | .vlam _ => .one
  | .vlet .. => .zero []

variable! (env : VEnv) (U : Nat) (Γ : List VExpr) in
inductive VLocalDecl.IsDefEq : VLocalDecl → VLocalDecl → Prop
  | vlam : env.IsDefEq U Γ type₁ type₂ (.sort u) → VLocalDecl.IsDefEq (.vlam type₁) (.vlam type₂)
  | vlet :
    env.IsDefEq U Γ value₁ value₂ type₁ → env.IsDefEq U Γ type₁ type₂ (.sort u) →
    VLocalDecl.IsDefEq (.vlet type₁ value₁) (.vlet type₂ value₂)

@[simp] theorem VLocalDecl.lift'_depth {d : VLocalDecl} : (d.lift' n).depth = d.depth := by
  cases d <;> rfl

theorem VLocalDecl.lift'_comp {d : VLocalDecl} : d.lift' (.comp l₁ l₂) = (d.lift' l₁).lift' l₂ := by
  cases d <;> simp [VLocalDecl.lift', VExpr.lift'_comp]

namespace VLCtx

variable! (henv : Ordered env) in
theorem WF.find?_wf {Δ : VLCtx} (hΔ : WF env U Δ) (H : Δ.find? v = some (e, A)) :
    env.HasType U Δ.toCtx e A := by
  let (ofv, d') :: Δ := Δ
  unfold find? at H; split at H
  · cases H; exact hΔ.2.2.hasType
  · simp at H
    obtain ⟨d'', n', H, rfl, rfl⟩ := H
    obtain h3 := hΔ.1.find?_wf H
    exact h3.weakN henv VLocalDecl.is_liftN

theorem WF.toCtx : ∀ {Δ}, WF env U Δ → OnCtx Δ.toCtx (env.IsType U)
  | [], _ => ⟨⟩
  | (_, .vlam _) :: _, ⟨hΔ, _, hA⟩ => ⟨hΔ.toCtx, hA⟩
  | (_, .vlet ..) :: _, ⟨hΔ, _, _⟩ => hΔ.toCtx

instance : Coe (WF env U Δ) (OnCtx Δ.toCtx (env.IsType U)) := ⟨(·.toCtx)⟩

theorem WF.fvars_nodup : ∀ {Δ}, WF env U Δ → Δ.fvars.Nodup
  | [], _ => .nil
  | (none, _) :: Δ, ⟨hΔ, _, _⟩ => fvars_nodup (Δ := Δ) hΔ
  | (some (fv, _), _) :: Δ, ⟨hΔ,  h, _⟩ => by
    suffices fv ∉ fvars Δ from (fvars_nodup hΔ).cons (fun _ h (e:fv=_) => this (e ▸ h))
    exact (h _ _ rfl).1

theorem fvars_nodup_tail {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    {Δ : VLCtx} (h : (fvars ((ofv, d) :: Δ)).Nodup) : Δ.fvars.Nodup := by
  cases ofv with
  | none => exact h
  | some fv => exact (List.nodup_cons.1 h).2

theorem liftVar_zero : liftVar 0 k v = v := by cases v <;> simp [liftVar]

inductive FVLift' : VLCtx → VLCtx → Nat → Lift → Nat → Prop
  | refl : FVLift' Δ Δ 0 .refl 0
  | skip_fvar (fv d) : FVLift' Δ Δ' 0 n 0 →
    FVLift' Δ ((some fv, d) :: Δ') 0 (n.skipN d.depth) 0
  | cons_fvar (fv d) : fv.2 ⊆ Δ.fvars → FVLift' Δ Δ' 0 n 0 →
    FVLift' ((some fv, d) :: Δ) ((some fv, d.lift' n) :: Δ') 0 (.consN n d.depth) 0
  | cons_bvar (d) : FVLift' Δ Δ' dk n k →
    FVLift' ((none, d) :: Δ) ((none, d.lift' (n.consN k)) :: Δ') (dk + 1) n (k + d.depth)

protected theorem FVLift'.toCtx (W : FVLift' Δ Δ' dk n k) :
    Ctx.Lift' (n.consN k) Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .refl
  | skip_fvar _ d _ ih => match d with
    | .vlet .. => exact ih
    | .vlam A => exact .skip ih
  | cons_fvar _ d _ _ ih => match d with
    | .vlet .. => exact ih
    | .vlam A => exact .cons ih
  | cons_bvar d _ ih => match d with
    | .vlet .. => exact ih
    | .vlam A => exact .cons ih

theorem FVLift'.comp (H1 : FVLift' Δ₁ Δ₂ 0 n₁ 0) (H2 : FVLift' Δ₂ Δ₃ dk n₂ k) :
    FVLift' Δ₁ Δ₃ dk (n₁.comp n₂) k := by
  induction H2 generalizing n₁ Δ₁ with
  | refl => exact H1
  | skip_fvar _ _ _ ih => simpa [Lift.comp_skipN] using (ih H1).skip_fvar _ _
  | cons_fvar _ d h1 _ ih => cases H1 with
    | refl => simpa using (ih .refl).cons_fvar _ _ h1
    | skip_fvar _ _ h2 => simpa [Lift.skipN_comp_consN] using (ih h2).skip_fvar _ (d.lift' _)
    | cons_fvar _ d h1 h2 =>
      simpa [← Lift.consN_comp, ← VLocalDecl.lift'_comp] using (ih h2).cons_fvar _ d h1
  | cons_bvar d h1 ih => cases H1 with | refl => simpa using h1.cons_bvar _

theorem FVLift'.from_nil : ∀ {Δ : VLCtx}, Δ.NoBV → FVLift' [] Δ 0 (.skipN .refl Δ.toCtx.length) 0
  | [], _ => .refl
  | (some _, .vlam _) :: _, H => .skip_fvar _ _ (.from_nil H)
  | (some _, .vlet _ _) :: _, H => .skip_fvar _ _ (.from_nil H)

theorem FVLift'.fvars_sublist (W : FVLift' Δ Δ' dk n k) : Δ.fvars <+ Δ'.fvars := by
  induction W with
  | refl => exact .refl _
  | skip_fvar _ _ _ ih => exact .cons _ ih
  | cons_fvar _ _ _ _ ih => exact .cons_cons _ ih
  | cons_bvar _ _ ih => exact ih

theorem FVLift'.bvars_eq (W : FVLift' Δ Δ' dk n k) : Δ'.bvars = Δ.bvars := by
  induction W with
  | refl => rfl
  | skip_fvar _ _ _ ih => exact ih
  | cons_fvar _ _ _ _ ih => exact ih
  | cons_bvar _ _ ih => exact congrArg Nat.succ ih

/-- Weakening of a lookup along `FVLift'`. Only the distinctness of the free variables of the
larger context is needed (`VLCtx.WF.fvars_nodup` provides it for a well-formed one). -/
protected theorem FVLift'.find? (W : FVLift' Δ Δ' dk n k) (hnd : Δ'.fvars.Nodup)
    (H : find? Δ v = some (e, A)) :
    find? Δ' v = some (e.lift' (n.consN k), A.lift' (n.consN k)) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | skip_fvar fv' _ W ih =>
    let (fv', deps) := fv'; simp [find?]
    cases v with simp [next]
    | inl =>
      refine ⟨_, _, ih (fvars_nodup_tail hnd) H, ?_⟩
      simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · refine ⟨_, _, ih (fvars_nodup_tail hnd) H, ?_⟩
        simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
      · refine ((List.pairwise_cons.1 hnd).1 fv' ?_ rfl).elim
        exact W.fvars_sublist.subset ((beq_iff_eq ..).1 eq ▸ find?_eq_some.1 ⟨_, H⟩)
  | cons_fvar fv' d _ W ih =>
    let (fv', deps) := fv'; revert H; simp [find?]
    have hnd' := fvars_nodup_tail hnd
    obtain i | fv := v <;> simp [next] <;>
      [skip; cases eq : fv' == fv <;> simp] <;>
      [(rintro _ _ H rfl rfl; refine ⟨_, _, ih hnd' H, ?_⟩);
       (rintro _ _ H rfl rfl; refine ⟨_, _, ih (v := .inr fv) hnd' H, ?_⟩);
       rintro rfl rfl] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]
  | cons_bvar d _ ih =>
    simp [find?] at H ⊢
    have hnd' := fvars_nodup_tail hnd
    obtain ⟨_|i⟩ | fv := v <;> simp [next] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inl i) hnd' H, ?_⟩);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inr fv) hnd' H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]

inductive FVLift : VLCtx → VLCtx → Nat → Nat → Nat → Prop
  | refl : FVLift Δ Δ 0 0 0
  | skip_fvar (fv d) : FVLift Δ Δ' 0 n 0 → FVLift Δ ((some fv, d) :: Δ') 0 (n + d.depth) 0
  | cons_bvar (d) : FVLift Δ Δ' dk n k →
    FVLift ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') (dk + 1) n (k + d.depth)

theorem FVLift.toFVLift' (W : FVLift Δ Δ' dk n k) : FVLift' Δ Δ' dk (.skipN .refl n) k := by
  induction W with
  | refl => exact .refl
  | skip_fvar fv d _ ih => simpa [Lift.skipN_skipN] using ih.skip_fvar fv d
  | cons_bvar d _ ih =>
    simpa [← VLocalDecl.lift'_consN_skipN, Lift.skipN_skipN] using ih.cons_bvar d

protected theorem FVLift.toCtx (W : FVLift Δ Δ' dk n k) : Ctx.LiftN n k Δ.toCtx Δ'.toCtx :=
  Ctx.liftN_iff_lift'.2 W.toFVLift'.toCtx

theorem FVLift.from_nil : ∀ {Δ : VLCtx}, Δ.NoBV → FVLift [] Δ 0 Δ.toCtx.length 0
  | [], _ => .refl
  | (some _, .vlam _) :: _, H => .skip_fvar _ _ (.from_nil H)
  | (some _, .vlet _ _) :: _, H => .skip_fvar _ _ (.from_nil H)

/-- Adding a free-variable-only prefix is an `FVLift` of the retained suffix.
Unlike `from_nil`, this form keeps an arbitrary suffix available for a later
cached-variable abstraction. -/
theorem FVLift.to_append (suffix : VLCtx) : ∀ {added : VLCtx},
    added.NoBV →
    FVLift suffix (added ++ suffix) 0 added.toCtx.length 0
  | [], _ => .refl
  | (some _, .vlam _) :: added, H =>
      .skip_fvar _ _ (to_append suffix (added := added) H)
  | (some _, .vlet _ _) :: added, H =>
      .skip_fvar _ _ (to_append suffix (added := added) H)

theorem FVLift.wf_of_zero (W : FVLift Δ Δ' dk n k) (h0 : dk = 0)
    (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip_fvar _ _ _ ih => exact ih h0 hΔ'.1
  | cons_bvar _ _ _ => exact absurd h0 (Nat.succ_ne_zero _)

/-- Dropping a free-variable prefix with no bound variables above it keeps
well-formedness: the retained context is literally a tail. -/
theorem FVLift.wf (_henv : VEnv.WF env) (W : FVLift Δ Δ' 0 n 0)
    (hΔ' : Δ'.WF env U) : Δ.WF env U :=
  W.wf_of_zero rfl hΔ'

theorem FVLift.fvars_suffix (W : FVLift Δ Δ' dk n k) : Δ.fvars <:+ Δ'.fvars := by
  induction W with
  | refl => exact List.suffix_refl _
  | skip_fvar _ _ _ ih => exact ih.trans (List.suffix_cons ..)
  | cons_bvar _ _ ih => exact ih

protected theorem FVLift.find? (W : FVLift Δ Δ' dk n k) (hnd : Δ'.fvars.Nodup)
    (H : find? Δ v = some (e, A)) : find? Δ' v = some (e.liftN n k, A.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using W.toFVLift'.find? hnd H

inductive BVLift : (Δ Δ' : VLCtx) → (dn dk n k : Nat) → Prop
  | refl : BVLift Δ Δ 0 0 0 0
  | skip (d) : BVLift Δ Δ' dn 0 n 0 → BVLift Δ ((none, d) :: Δ') (dn + 1) 0 (n + d.depth) 0
  | cons (d) : BVLift Δ Δ' dn dk n k →
    BVLift ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') dn (dk + 1) n (k + d.depth)

theorem BVLift.toCtx (W : BVLift Δ Δ' dn dk n k) : Ctx.LiftN n k Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .zero []
  | @skip _ Δ' _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A =>
      generalize hΓ' : VLCtx.toCtx Δ' = Γ' at ih
      let .zero As eq := ih
      simp [VLCtx.toCtx, hΓ']
      exact .zero (A :: As) (eq ▸ rfl)
  | cons d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

theorem BVLift.fvars_eq (W : BVLift Δ Δ' dn dk n k) : Δ.fvars = Δ'.fvars := by
  induction W with
  | refl => rfl
  | skip _ _ ih => exact ih
  | cons _ _ ih => exact ih

protected theorem BVLift.find? (W : BVLift Δ Δ' dn dk n k) (H : find? Δ v = some (e, A)) :
    find? Δ' (liftVar dn dk v) = some (e.liftN n k, A.liftN n k) := by
  induction W generalizing v e A with
  | refl => simp [H, liftVar_zero]
  | @skip _ Δ' _ fv' _ W ih =>
    obtain v | fv := v <;> simp [find?, liftVar, next] <;>
      exact ⟨_, _, ih H, by simp [VExpr.liftN_liftN]⟩
  | cons d _ ih =>
    obtain (_ | v) | fv := v <;> simp [liftVar] <;>
      [ (simp [find?, next] at H ⊢; simp [← H]);
        split <;> (
          rename_i h
          simp [Nat.add_right_comm _ 1, find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          have := ih H
          simp [liftVar, h] at this
          refine ⟨_, _, this, ?_⟩);
        ( simp [find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          refine ⟨_, _, ih H, ?_⟩ )] <;>
      open VLocalDecl in
      cases d <;> simp [VExpr.lift_liftN', liftN, value, type, depth, VExpr.liftN]

/-- A lookup of a lifted variable in the larger context comes from the smaller one. -/
theorem BVLift.find?_lift_inv (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (h : Δ'.find? (VLCtx.liftVar dn dk v) = some p) : ∃ x, Δ.find? v = some x := by
  induction W generalizing v p with
  | refl => simp [VLCtx.liftVar_zero] at h; exact ⟨_, h⟩
  | skip d _ ih =>
    obtain i | fv := v
    · simp only [VLCtx.liftVar, Nat.not_lt_zero, if_false, ← Nat.add_assoc, VLCtx.find?,
        VLCtx.next, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      exact ih (v := .inl i) (by simpa [VLCtx.liftVar] using h)
    · simp only [VLCtx.liftVar, VLCtx.find?, VLCtx.next, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      exact ih (v := .inr fv) (by simpa [VLCtx.liftVar] using h)
  | @cons _ _ dn' dk' _ _ d _ ih =>
    obtain (_ | i) | fv := v
    · exact ⟨_, rfl⟩
    · have e : VLCtx.liftVar dn' (dk' + 1) (.inl (i + 1)) =
          .inl ((if i < dk' then i else i + dn') + 1) := by
        simp only [VLCtx.liftVar]; congr 1; split <;> split <;> omega
      rw [e] at h
      simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      obtain ⟨⟨e, A⟩, h'⟩ := ih (v := .inl i) (by simpa [VLCtx.liftVar] using h)
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h']⟩
    · simp only [VLCtx.liftVar, VLCtx.find?, VLCtx.next, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨_, h, -⟩ := h
      obtain ⟨⟨e, A⟩, h'⟩ := ih (v := .inr fv) (by simpa [VLCtx.liftVar] using h)
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h']⟩

variable (Δ₀ : VLCtx) (e₀ A₀ : VExpr) in
inductive InstN : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : InstN 0 0 ((none, .vlam A₀) :: Δ₀) Δ₀
  | succ : InstN dk k Γ Γ' → InstN (dk + 1) (k + d.depth) ((none, d)::Γ) ((none, d.inst e₀ k) :: Γ')

protected theorem InstN.toCtx (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Ctx.InstN Δ₀.toCtx e₀ A₀ k Δ₁.toCtx Δ.toCtx := by
  induction W with
  | zero => exact .zero
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

variable! (henv : Ordered env) (h₀ : env.HasType U (toCtx Δ₀) e₀ A₀) in
theorem InstN.wf (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact hΔ'.1
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, h2.instN henv W.toCtx h₀⟩

theorem InstN.fvars_eq (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Δ₁.fvars = Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

/-- The context after a substitution extends the context of the substituted term by the
binders below the substituted one. -/
theorem InstN.toBVLift (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) : BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ _ _ _ d _ ih => cases d <;> exact .skip _ ih

variable (Δ₀ : VLCtx) (e₀ A₀ : VExpr) in
inductive InstLet : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : InstLet 0 0 ((none, .vlet A₀ e₀) :: Δ₀) Δ₀
  | succ : InstLet dk k Γ Γ' → InstLet (dk + 1) (k + d.depth) ((none, d)::Γ) ((none, d) :: Γ')

protected theorem InstLet.toCtx (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) : Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => rfl
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam _ => exact congrArg (_::·) ih

theorem InstLet.wf (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact hΔ'.1
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, W.toCtx ▸ h2⟩

theorem InstLet.fvars_eq (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Δ₁.fvars = Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

theorem InstLet.toBVLift (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) : BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | succ _ ih => exact .skip _ ih

variable (Δ₀ : VLCtx) (v₀ : FVarId) (d₀ : VLocalDecl) in
inductive Abstract : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : Abstract 0 0 ((some (v₀, deps), d₀) :: Δ₀) ((none, d₀) :: Δ₀)
  | succ : Abstract dk k Γ Γ' → Abstract (dk + 1) (k + d.depth) ((none, d) :: Γ) ((none, d) :: Γ')

protected theorem Abstract.toCtx (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) : Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => cases d₀ <;> rfl
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact congrArg (_ :: ·) ih

theorem Abstract.wf (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact ⟨hΔ'.1, nofun, hΔ'.2.2⟩
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, W.toCtx ▸ h2⟩

theorem Abstract.fvars_eq (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) :
    Δ₁.fvars = v₀ :: Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

theorem Abstract.find?_self (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) :
    Δ₁.find? (.inr v₀) = some (d₀.value.liftN k, d₀.type.liftN k) := by
  induction W with simp [find?, next]
  | succ _ ih => exact ⟨_, _, ih, by simp [VExpr.liftN_liftN]⟩

protected theorem Abstract.find? (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (h : v ≠ .inr v₀) :
    Δ.find? v = Δ₁.find? (clear% h; match v with
      | .inl i => if i < dk then .inl i else if i = dk then .inr v₀ else .inl (i - 1)
      | .inr v' => .inr v') := by
  induction W generalizing v with
  | zero =>
    obtain (_|i)|v := v <;> simp [find?, next]
    cases eq : v₀ == v; · simp
    · simp at h eq; cases h eq.symm
  | @succ dk k _ _ _ _ ih =>
    obtain (_|i)|v := v <;> simp [find?, next]
    · have := @ih (.inl i) nofun; revert this
      by_cases h : i < dk <;> simp +contextual [h]
      by_cases h : i = dk <;> simp +contextual [h]
      obtain _|i := i <;> [omega; simp]
    · simp [ih h]

theorem instL_eq_map (Δ : VLCtx) : Δ.instL ls = Δ.map (fun (ofv, d) => (ofv, d.instL ls)) := by
  induction Δ <;> simp [instL, *]

@[simp] theorem instL_fvars (Δ : VLCtx) :
    (Δ.instL ls).fvars = Δ.fvars := by
  induction Δ with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨ofv, decl⟩
    rcases ofv with _ | ⟨fv, deps⟩
    · simpa [instL, fvars] using ih
    · simpa [instL, fvars] using congrArg (List.cons fv) ih

@[simp] theorem instL_toCtx (Δ : VLCtx) : (Δ.instL ls).toCtx = Δ.toCtx.map (·.instL ls) := by
  induction Δ with
  | nil => rfl
  | cons head => obtain ⟨_, _|_⟩ := head <;> rw [instL, VLocalDecl.instL] <;> simp [toCtx, *]

variable! (hls : ∀ l ∈ (ls : List _), VLevel.WF U l) in
protected theorem WF.instL : ∀ {Δ}, VLCtx.WF env ls.length Δ →
    VLCtx.WF env U (Δ.instL ls)
  | [], _ => ⟨⟩
  | (_, d) :: Δ, ⟨h1, h2, h3⟩ =>
    ⟨h1.instL, by simpa [instL_eq_map, fvars, Function.comp_def] using h2,
      by simpa using h3.instL hls⟩

theorem find?_instL : find? Δ v = some (e, A) →
    find? (Δ.instL ls) v = some (e.instL ls, A.instL ls) := by
  induction Δ generalizing v e A with
  | nil => nofun
  | cons d Δ ih =>
    simp [find?, instL]; split <;> simp
    · rintro rfl rfl; cases d.2 <;> exact ⟨rfl, by simp [VLocalDecl.instL, VLocalDecl.type]⟩
    · rintro e A h rfl rfl
      exact ⟨_, _, ih h, by cases d.2 <;> simp [VLocalDecl.instL, VLocalDecl.depth]⟩

variable (env : VEnv) (U) in
inductive SortList : VLCtx → List VLevel → Prop
  | nil : SortList Δ []
  | cons : SortList Δ ls → env.HasType U Δ.toCtx A (.sort u) →
    SortList ((some fv, .vlam A) :: Δ) (u :: ls)

end VLCtx

inductive TrExprS.IsUniqueDecl : VLocalDecl → VLocalDecl → Prop
  | vlam : IsUniqueDecl (.vlam ty) (.vlam ty')
  | vlet : IsUniqueDecl (.vlet ty val) (.vlet ty' val)

inductive TrExprS.IsUniqueCtx : VLCtx → VLCtx → Prop
  | base : IsUniqueCtx Δ Δ
  | cons : IsUniqueCtx Δ₁ Δ₂ → IsUniqueDecl d₁ d₂ → IsUniqueCtx ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem TrExprS.IsUniqueCtx.find?_uniq (hΔ : IsUniqueCtx Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) : e₁ = e₂ := by
  induction hΔ generalizing v e₁ e₂ A₁ A₂ with
  | base => cases H1.symm.trans H2; rfl
  | @cons _ _ _ _ ofv _ hd ih =>
    revert H1 H2; simp [VLCtx.find?]; split
    · rintro ⟨⟩ ⟨⟩; cases hd <;> rfl
    · simp; rintro _ _ h1 rfl rfl _ _ h2 rfl rfl
      congr 1
      · cases hd <;> rfl
      · exact ih h1 h2

/-- Lookups in contexts differing only in binder domains agree on the value. -/
theorem TrExprS.IsUniqueCtx.find?_exists {Δ₁ Δ₂ : VLCtx} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H : Δ₁.find? v = some (e, A)) : ∃ A', Δ₂.find? v = some (e, A') := by
  induction hΔ generalizing v e A with
  | base => exact ⟨A, H⟩
  | @cons _ _ _ _ ofv _ hd ih =>
    revert H; simp [VLCtx.find?]; split
    · intro h; cases h; cases hd <;> exact ⟨_, rfl⟩
    · simp; rintro _ _ h1 rfl rfl
      obtain ⟨A', h2⟩ := ih h1
      refine ⟨_, _, _, h2, ?_, rfl⟩
      cases hd <;> rfl

theorem ofLevel_hasMVar (h : VLevel.ofLevel ls l = some l') : l.hasMVar' = false := by
  induction l generalizing l' with simp [VLevel.ofLevel, bind, Level.hasMVar'] at h ⊢
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact ih h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩

end Lean4Lean
