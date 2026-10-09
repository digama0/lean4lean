import Lean4Lean.Verify.Inductive.Nested.Restoration.Commutation
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorShape
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Contexts
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Theory.Inductive.CaseCertificateMono

/-! Nested expansions whose leaves are inverted by a restoration table.

`Restoration.RestoringLeaf r levels` is the leaf relation "the restoration of
the target is the source", conditional on the source avoiding the restorable
names and on every restoration head in the target occurring at the universe
arguments `levels`. A structural expansion with these leaves is inverted by
`Restoration.expr` (`VExpr.NestedExprExpansion.restore`), and the leaf relation
is stable under lifting, so it can be produced by the generic absolute-depth
projection of the lowering relation (`NestedExpansionLeafLiftAbove`).
-/

namespace Lean4Lean

/-- Every occurrence of a constant in `names` has universe arguments
`levels`. -/
def VExpr.ConstLevelsAt (names : List Lean.Name) (levels : List VLevel) : VExpr → Prop
  | .const c ls => c ∈ names → ls = levels
  | .app f a | .lam f a | .forallE f a =>
    f.ConstLevelsAt names levels ∧ a.ConstLevelsAt names levels
  | .proj _ _ e => e.ConstLevelsAt names levels
  | .bvar _ | .sort _ | .elim .. => True

@[simp] theorem VExpr.constLevelsAt_liftN (e : VExpr) (names : List Lean.Name)
    (levels : List VLevel) (n k : Nat) :
    (e.liftN n k).ConstLevelsAt names levels ↔ e.ConstLevelsAt names levels := by
  induction e generalizing k <;> simp [VExpr.liftN, VExpr.ConstLevelsAt, *]

theorem VExpr.constLevelsAt_mkApps {names : List Lean.Name} {levels : List VLevel} :
    ∀ {fn : VExpr} {args : List VExpr},
      (VExpr.mkApps fn args).ConstLevelsAt names levels ↔
        fn.ConstLevelsAt names levels ∧ ∀ arg ∈ args, arg.ConstLevelsAt names levels
  | fn, [] => by simp [VExpr.mkApps]
  | fn, arg :: args => by
    rw [show VExpr.mkApps fn (arg :: args) = VExpr.mkApps (.app fn arg) args from rfl,
      VExpr.constLevelsAt_mkApps]
    simp [VExpr.ConstLevelsAt, and_assoc]

namespace InductiveSignature

theorem HeadSpecialization.apply_append {h : HeadSpecialization} {levels : List VLevel}
    {args : List VExpr} {x : VExpr} (H : h.apply levels args = some x) (extra : List VExpr) :
    h.apply levels (args ++ extra) = some (VExpr.mkApps x extra) := by
  unfold HeadSpecialization.apply at H ⊢
  split at H
  · cases H
  · rename_i hgood
    have hlen : h.nparams ≤ args.length := by
      apply Nat.le_of_not_gt
      intro ht
      simp [ht] at hgood
    have hgood' : ¬((levels.length != h.uvars || (args ++ extra).length < h.nparams) =
        true) := by
      simp only [List.length_append, Bool.or_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq, not_or, Classical.not_not, Nat.not_lt] at hgood ⊢
      exact ⟨hgood.1, by omega⟩
    simp only [hgood']
    simp only [Option.pure_def, Option.some.injEq] at H ⊢
    subst H
    rw [List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen,
      ← List.append_assoc, VExpr.mkApps_append]
    rfl

/-- Restoration of an application spine whose head restores extends to any
further arguments. -/
theorem Restoration.expr.go_append (r : Restoration) :
    ∀ (e : VExpr) {args₀ : List VExpr} {x : VExpr},
      Restoration.expr.go r e args₀ = some x → ∀ extra,
        Restoration.expr.go r e (args₀ ++ extra) = some (VExpr.mkApps x extra)
  | .app fn arg, args₀, x, H, extra => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H ⊢
    cases ha : Restoration.expr.go r arg [] with
    | none => rw [ha] at H; cases H
    | some a' =>
      rw [ha] at H
      simp only [Option.bind_some] at H ⊢
      exact Restoration.expr.go_append r fn (args₀ := a' :: args₀) H extra
  | .const name levels, args₀, x, H, extra => by
    simp only [Restoration.expr.go] at H ⊢
    split at H
    · exact HeadSpecialization.apply_append H extra
    · cases H
      exact congrArg some (VExpr.mkApps_append _ _ _)
  | .bvar _, _, x, H, extra | .sort _, _, x, H, extra | .elim .., _, x, H, extra => by
    simp only [Restoration.expr.go, Option.some.injEq] at H ⊢
    subst H
    exact VExpr.mkApps_append _ _ _
  | .lam domain body, args₀, x, H, extra
  | .forallE domain body, args₀, x, H, extra => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H ⊢
    cases hd : Restoration.expr.go r domain [] <;>
      cases hb : Restoration.expr.go r body [] <;>
      simp only [hd, hb, Option.bind_none, Option.bind_some, Option.pure_def,
        Option.some.injEq, reduceCtorEq] at H ⊢
    subst H
    exact VExpr.mkApps_append _ _ _
  | .proj name i major, args₀, x, H, extra => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H ⊢
    cases hm : Restoration.expr.go r major [] <;>
      simp only [hm, Option.bind_none, Option.bind_some, Option.pure_def,
        Option.some.injEq, reduceCtorEq] at H ⊢
    subst H
    exact VExpr.mkApps_append _ _ _

/-- Leaves inverted by a restoration table: the restoration of the target is
the source, whenever the source avoids the restorable names and every head of
the table occurs in the target at universe arguments `levels`. -/
def Restoration.RestoringLeaf (r : Restoration) (levels : List VLevel) :
    Nat → VExpr → VExpr → Prop :=
  fun _ source target =>
    source.containsAnyConst r.restorableNames = false →
    target.ConstLevelsAt (r.heads.map (·.auxiliary)) levels →
    r.expr target = some source

/-- An expansion whose leaves are restoring is inverted by restoration. -/
theorem _root_.Lean4Lean.VExpr.NestedExprExpansion.restore {r : Restoration}
    {levels : List VLevel} {depth : Nat} {source target : VExpr}
    (H : VExpr.NestedExprExpansion (r.RestoringLeaf levels) depth source target)
    (hs : source.containsAnyConst r.restorableNames = false)
    (ht : target.ConstLevelsAt (r.heads.map (·.auxiliary)) levels) :
    r.expr target = some source := by
  induction H with
  | occurrence h => exact h hs ht
  | bvar | sort | elim => rfl
  | const => exact Restoration.expr_of_avoid hs
  | proj _ ih =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hs
    have h := ih hs.2 ht
    simp only [Restoration.expr] at h ⊢
    simp [Restoration.expr.go, h, VExpr.mkApps]
  | app _ _ ihf iha =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hs
    have hf := ihf hs.1 ht.1
    have ha := iha hs.2 ht.2
    simp only [Restoration.expr] at hf ha ⊢
    simp only [Restoration.expr.go, ha, Option.bind_eq_bind, Option.bind_some]
    exact Restoration.expr.go_append r _ (args₀ := []) hf [_]
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hs
    have hd := ihd hs.1 ht.1
    have hb := ihb hs.2 ht.2
    simp only [Restoration.expr] at hd hb ⊢
    simp [Restoration.expr.go, hd, hb, VExpr.mkApps]

/-- Pointwise restoration of expansion-related argument lists. -/
theorem _root_.Lean4Lean.VExpr.NestedExprExpansion.forall₂_restore {r : Restoration}
    {levels : List VLevel} {depth : Nat} :
    ∀ {sources targets : List VExpr},
      List.Forall₂ (VExpr.NestedExprExpansion (r.RestoringLeaf levels) depth)
        sources targets →
      (∀ s ∈ sources, s.containsAnyConst r.restorableNames = false) →
      (∀ t ∈ targets, t.ConstLevelsAt (r.heads.map (·.auxiliary)) levels) →
      List.Forall₂ (fun t s => Restoration.expr.go r t [] = some s) targets sources
  | [], [], .nil, _, _ => .nil
  | _ :: _, _ :: _, .cons h t, hs, ht =>
    .cons (h.restore (hs _ List.mem_cons_self) (ht _ List.mem_cons_self))
      (VExpr.NestedExprExpansion.forall₂_restore t
        (fun s hsMem => hs s (List.mem_cons_of_mem _ hsMem))
        (fun s hsMem => ht s (List.mem_cons_of_mem _ hsMem)))

/-- Restoring leaves are stable under every binder lift. -/
theorem Restoration.restoringLeaf_liftAbove (r : Restoration)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (levels : List VLevel) (np : Nat) :
    VerifyInductive.NestedExpansionLeafLiftAbove np (r.RestoringLeaf levels) := by
  intro depth source target cutoff _ H hs ht
  rw [VExpr.containsAnyConst_liftN] at hs
  rw [VExpr.constLevelsAt_liftN] at ht
  rw [← Restoration.expr_liftN r hc, H hs ht]
  rfl

end InductiveSignature

/-! ### Universe arguments of restoration heads in an expansion -/

/-- Leaves whose target uses the constants `names` only at the universe
arguments `levels`, whenever the source does not mention `names`. -/
def VExpr.LevelLeaf (names : List Lean.Name) (levels : List VLevel) :
    Nat → VExpr → VExpr → Prop :=
  fun _ source target =>
    source.containsAnyConst names = false → target.ConstLevelsAt names levels

/-- Level leaves are stable under every binder lift. -/
theorem VExpr.levelLeaf_liftAbove (names : List Lean.Name) (levels : List VLevel)
    (np : Nat) :
    VerifyInductive.NestedExpansionLeafLiftAbove np (VExpr.LevelLeaf names levels) := by
  intro depth source target cutoff _ H hs
  rw [VExpr.containsAnyConst_liftN] at hs
  rw [VExpr.constLevelsAt_liftN]
  exact H hs

/-- An expansion of a source avoiding `names`, all of whose leaves are level
leaves, uses `names` only at `levels`: away from the leaves the target copies
the source. -/
theorem VExpr.NestedExprExpansion.constLevelsAt {names : List Lean.Name}
    {levels : List VLevel} {leaf : Nat → VExpr → VExpr → Prop}
    (Hleaf : ∀ {depth source target}, leaf depth source target →
      VExpr.LevelLeaf names levels depth source target)
    {depth : Nat} {source target : VExpr}
    (H : VExpr.NestedExprExpansion leaf depth source target)
    (hs : source.containsAnyConst names = false) :
    target.ConstLevelsAt names levels := by
  induction H with
  | occurrence h => exact Hleaf h hs
  | bvar | sort | elim => trivial
  | const =>
    intro hmem
    simp only [VExpr.containsAnyConst] at hs
    simp [hmem] at hs
  | proj _ ih =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hs
    exact ih hs.2
  | app _ _ ihf iha | lam _ _ ihf iha | forallE _ _ ihf iha =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at hs
    exact ⟨ihf hs.1, iha hs.2⟩

end Lean4Lean
