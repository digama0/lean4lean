import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Typing.Expr

/-! # Syntactic forall and lambda telescopes

The relations here record the leading binders and residuals of executable expressions,
without typing or inductive-checker state. Abstraction and instantiation preserve the exact
binder count, and the shared-prefix relations identify literal binder domains. Typed
translation certificates and checker-specific closure lemmas remain in
`Verify.Inductive.Recursor.Context.ForallTelescope`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

theorem Expr.lastRevIdx?_append (v : FVarId) : ∀ (ys zs : List FVarId),
    Expr.lastRevIdx? v (ys ++ zs) =
      match Expr.lastRevIdx? v zs with
      | some r => some r
      | none => (Expr.lastRevIdx? v ys).map (· + zs.length)
  | [], zs => by cases h : Expr.lastRevIdx? v zs <;> simp [Expr.lastRevIdx?, h]
  | y :: ys, zs => by
    simp only [List.cons_append, Expr.lastRevIdx?, Expr.lastRevIdx?_append v ys zs]
    cases hz : Expr.lastRevIdx? v zs with
    | some r => simp
    | none =>
      cases hy : Expr.lastRevIdx? v ys with
      | some r => simp
      | none => by_cases hyv : (y == v) = true <;> simp [hyv, List.length_append]

/-- Abstracting a concatenation is abstracting the suffix first, then the prefix below the
suffix's binders. -/
theorem Expr.abstractN_append (ys zs : List FVarId) : ∀ (e : Expr) (d : Nat),
    e.abstractN (ys ++ zs) d = (e.abstractN zs d).abstractN ys (d + zs.length)
  | .bvar _, _ => rfl
  | .fvar v, d => by
    simp only [Expr.abstractN, Expr.lastRevIdx?_append]
    cases hz : Expr.lastRevIdx? v zs with
    | some r => simp [Expr.abstractN]
    | none =>
      cases hy : Expr.lastRevIdx? v ys with
      | some r => simp [Expr.abstractN, hy, Nat.add_comm, Nat.add_left_comm]
      | none => simp [Expr.abstractN, hy]
  | .mdata _ e, d => by simp [Expr.abstractN, Expr.abstractN_append ys zs e d]
  | .proj _ _ e, d => by simp [Expr.abstractN, Expr.abstractN_append ys zs e d]
  | .app f a, d => by
    simp [Expr.abstractN, Expr.abstractN_append ys zs f d, Expr.abstractN_append ys zs a d]
  | .lam _ t b _, d => by
    simp [Expr.abstractN, Expr.abstractN_append ys zs t d, Expr.abstractN_append ys zs b (d+1),
      Nat.add_right_comm]
  | .forallE _ t b _, d => by
    simp [Expr.abstractN, Expr.abstractN_append ys zs t d, Expr.abstractN_append ys zs b (d+1),
      Nat.add_right_comm]
  | .letE _ t v b _, d => by
    simp [Expr.abstractN, Expr.abstractN_append ys zs t d, Expr.abstractN_append ys zs v d,
      Expr.abstractN_append ys zs b (d+1), Nat.add_right_comm]
  | .const .., _ | .sort _, _ | .mvar _, _ | .lit _, _ => rfl


/-- An expression consists of `arity` leading forall binders and the residual body
`result`. Binder domains are not recorded: `VInductDecl.RecursorShape` records them
existentially and constrains only their number. -/
inductive Expr.ForallTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : ForallTelescope body 0 body
  | cons : ForallTelescope body arity result →
      ForallTelescope (.forallE name dom body bi) (arity + 1) result

theorem Expr.ForallTelescope.trans
    (Houter : Expr.ForallTelescope outer outerArity middle)
    (Hinner : Expr.ForallTelescope middle innerArity result) :
    Expr.ForallTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.ForallTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

/-- Abstracting one retained free variable preserves telescope arity; the
residual body is abstracted below all telescope binders. -/
theorem Expr.ForallTelescope.abstract1
    (H : Expr.ForallTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Simultaneous abstraction is the iterated form of `abstract1` and likewise
preserves the exact leading telescope. -/
theorem Expr.ForallTelescope.abstractList
    (H : Expr.ForallTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Simultaneous abstraction preserves the exact leading telescope; the cutoff advances
below the retained binders. -/
theorem Expr.ForallTelescope.abstractN
    (H : Expr.ForallTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstractN fvs k) arity
      (result.abstractN fvs (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstractN]
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- A closed telescope has a result closed at the depth of its binders. -/
theorem Expr.ForallTelescope.closed_result
    (H : Expr.ForallTelescope outer arity result) (Houter : Closed outer depth) :
    Closed result (depth + arity) := by
  induction H generalizing depth with
  | nil => simpa using Houter
  | cons _ ih =>
    have Hresult := ih Houter.2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- Instantiating below a forall telescope preserves its arity and performs
the same instantiation below all retained binders in the residual. -/
theorem Expr.ForallTelescope.instantiate1'
    (H : Expr.ForallTelescope outer arity result)
    (arg : Expr) (k : Nat := 0) :
    Expr.ForallTelescope (outer.instantiate1' arg k) arity
      (result.instantiate1' arg (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.instantiate1']
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Inserting loose bound variables below a forall telescope preserves its
arity; the insertion cutoff advances once beneath each retained binder. -/
theorem Expr.ForallTelescope.liftLooseBVars'
    (H : Expr.ForallTelescope outer arity result)
    (k amount : Nat) :
    Expr.ForallTelescope (outer.liftLooseBVars' k amount) arity
      (result.liftLooseBVars' (k + arity) amount) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.liftLooseBVars']
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.ForallTelescope.isForall_of_pos
    (H : Expr.ForallTelescope outer arity residual) (hpos : 0 < arity) :
    outer.isForall = true := by
  cases H with
  | nil => simp at hpos
  | cons => rfl

/-- For a fixed source and exact arity, the residual of a forall telescope
is unique.  Maximality is needed only when comparing different arities. -/
theorem Expr.ForallTelescope.residual_eq
    (Hleft : Expr.ForallTelescope source arity leftResidual)
    (Hright : Expr.ForallTelescope source arity rightResidual) :
    leftResidual = rightResidual := by
  induction Hleft with
  | nil => cases Hright; rfl
  | cons Htail ih =>
    cases Hright with
    | cons HrightTail => exact ih HrightTail

/-- A maximal forall decomposition is unique.  This is deliberately stated
with a non-forall condition on both residuals: without maximality, the same
source admits every shorter prefix as another `ForallTelescope`. -/
theorem Expr.ForallTelescope.eq_of_residual_not_forall
    (Hleft : Expr.ForallTelescope source leftArity leftResidual)
    (Hright : Expr.ForallTelescope source rightArity rightResidual)
    (hleft : leftResidual.isForall = false)
    (hright : rightResidual.isForall = false) :
    leftArity = rightArity ∧ leftResidual = rightResidual := by
  induction Hleft generalizing rightArity rightResidual with
  | nil =>
    cases Hright with
    | nil => exact ⟨rfl, rfl⟩
    | cons Htail => simp [Expr.isForall] at hleft
  | @cons body leftArity leftResidual name dom bi Hleft ih =>
    cases Hright with
    | nil => simp [Expr.isForall] at hright
    | cons Hright =>
      rcases ih Hright hleft hright with ⟨harity, hresidual⟩
      exact ⟨by omega, hresidual⟩

/-- Substituting a free variable cannot create a leading forall, so a telescope of the
instantiated expression gives one of the same arity for the expression itself. -/
theorem Expr.ForallTelescope.reflect_instantiate1'_fvar
    (H : Expr.ForallTelescope
      (e.instantiate1' (.fvar fv) k) arity residual) :
    ∃ sourceResidual, Expr.ForallTelescope e arity sourceResidual := by
  induction arity generalizing e residual k with
  | zero => exact ⟨e, .nil _⟩
  | succ arity ih =>
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.instantiate1'] at H
      cases H with
      | cons Htail =>
        rcases ih Htail with ⟨sourceResidual, Hsource⟩
        exact ⟨sourceResidual, .cons Hsource⟩
    | bvar i =>
      by_cases hlt : i < k
      · simp only [Expr.instantiate1', hlt, ↓reduceIte] at H
        exact Bool.noConfusion (H.isForall_of_pos (by omega))
      · by_cases heq : i = k
        · subst i
          simp only [Expr.instantiate1', Nat.lt_irrefl, ↓reduceIte] at H
          rw [Expr.liftLooseBVars_eq_self
            (by simp [Expr.looseBVarRange'])] at H
          exact Bool.noConfusion (H.isForall_of_pos (by omega))
        · simp only [Expr.instantiate1', hlt, heq, ↓reduceIte] at H
          exact Bool.noConfusion (H.isForall_of_pos (by omega))
    | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      simp only [Expr.instantiate1'] at H
      have hfor := H.isForall_of_pos (by omega)
      exact Bool.noConfusion hfor

/-- The domain at position `i` of a forall telescope. Unlike `Expr.ForallTelescope` it
carries no residual body; it identifies which local declaration the executable closed at
a given binder of a generated recursor type. -/
inductive Expr.ForallBinderAt : Expr → Nat → Expr → Prop
  | here : Expr.ForallBinderAt (.forallE name domain body bi) 0 domain
  | there : Expr.ForallBinderAt body i domain →
      Expr.ForallBinderAt (.forallE name outerDomain body bi) (i + 1) domain

theorem Expr.ForallBinderAt.unique
    (H₁ : Expr.ForallBinderAt source i domain₁)
    (H₂ : Expr.ForallBinderAt source i domain₂) : domain₁ = domain₂ := by
  induction H₁ with
  | @here name domain body bi =>
      cases H₂
      rfl
  | there _ ih =>
      cases H₂ with
      | there H₂ => exact ih H₂

/-- A selected forall domain inherits every free-variable restriction of
the enclosing telescope. -/
theorem Expr.ForallBinderAt.domainFVarsIn
    (H : Expr.ForallBinderAt source i domain)
    (Hsource : source.FVarsIn P) : domain.FVarsIn P := by
  induction H with
  | here => exact Hsource.1
  | there _ ih => exact ih Hsource.2

/-- Abstraction of a free variable through a forall prefix reaches the
selected domain below exactly the number of preceding binders. -/
theorem Expr.ForallBinderAt.abstract1
    (H : Expr.ForallBinderAt source i domain) (fv : FVarId) (k : Nat := 0) :
    Expr.ForallBinderAt (source.abstract1 fv k) i
      (domain.abstract1 fv (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.abstract1] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.abstract1 fv (k + 1))
          (bi := bi) (domain := domain.abstract1 fv k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.abstract1 fv k)
        (bi := bi) Htail
      simpa [Expr.abstract1, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.abstractN
    (H : Expr.ForallBinderAt source i domain) (xs : List FVarId) (k : Nat := 0) :
    Expr.ForallBinderAt (source.abstractN xs k) i
      (domain.abstractN xs (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.abstractN] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.abstractN xs (k + 1))
          (bi := bi) (domain := domain.abstractN xs k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.abstractN xs k)
        (bi := bi) Htail
      simpa [Expr.abstractN, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.abstractList
    (H : Expr.ForallBinderAt source i domain)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.ForallBinderAt (source.abstractList fvars k) i
      (domain.abstractList fvars (k + i)) := by
  induction fvars generalizing source domain with
  | nil => simpa using H
  | cons fv fvars ih =>
      simpa only [Expr.abstractList] using
        ih (H.abstract1 fv k)

/-- Prepending a concrete forall telescope shifts the position of a selected
binder by exactly the prefix arity. -/
theorem Expr.ForallTelescope.prependBinderAt
    (Hprefix : Expr.ForallTelescope outer prefixArity middle)
    (Hbinder : Expr.ForallBinderAt middle i domain) :
    Expr.ForallBinderAt outer (prefixArity + i) domain := by
  induction Hprefix with
  | nil => simpa using Hbinder
  | @cons body arity result name outerDomain bi Hprefix ih =>
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain) (bi := bi) (ih Hbinder)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- `inferImplicit` changes binder annotations but preserves every concrete
forall domain at its original position. -/
theorem Expr.ForallBinderAt.inferImplicit
    (H : Expr.ForallBinderAt source i domain)
    (max : Nat) (inferBinderTypes : Bool) :
    Expr.ForallBinderAt (source.inferImplicit max inferBinderTypes) i domain := by
  induction H generalizing max with
  | @here name domain body bi =>
      cases max with
      | zero => simpa [Expr.inferImplicit] using
          (Expr.ForallBinderAt.here (name := name) (body := body)
            (bi := bi) (domain := domain))
      | succ max =>
          simpa [Expr.inferImplicit] using
            (Expr.ForallBinderAt.here (name := name)
              (body := body.inferImplicit max inferBinderTypes)
              (bi := if bi.isExplicit &&
                (body.inferImplicit max inferBinderTypes).hasLooseBVarInExplicitDomain
                  0 inferBinderTypes then .implicit else bi)
              (domain := domain))
  | @there body i domain name outerDomain bi H ih =>
      cases max with
      | zero => simpa [Expr.inferImplicit] using
          (Expr.ForallBinderAt.there (name := name)
            (outerDomain := outerDomain) (bi := bi) H)
      | succ max =>
          have Htail := ih max
          simpa [Expr.inferImplicit] using
            (Expr.ForallBinderAt.there (name := name)
              (outerDomain := outerDomain)
              (bi := if bi.isExplicit &&
                (body.inferImplicit max inferBinderTypes).hasLooseBVarInExplicitDomain
                  0 inferBinderTypes then .implicit else bi)
              Htail)

/-- A prefix decomposition followed by one explicit forall identifies the
domain at that prefix position. -/
theorem Expr.ForallTelescope.binderAt
    (H : Expr.ForallTelescope source i suffix)
    (hsuffix : suffix = .forallE name domain body bi) :
    Expr.ForallBinderAt source i domain := by
  induction H with
  | nil =>
      rw [hsuffix]
      exact .here
  | cons _ ih =>
      exact .there (ih hsuffix)

/-- A concrete expression consists of exactly `arity` leading lambda binders
and the indicated residual body. -/
inductive Expr.LambdaTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : LambdaTelescope body 0 body
  | cons : LambdaTelescope body arity result →
      LambdaTelescope (.lam name dom body bi) (arity + 1) result

/-- Two expressions have the same leading lambda binders, while their residual bodies may
differ. Generated recursive calls and the eta-expanded fields used as their major premises
are related in this way: the executable closes both over the same local declarations. -/
inductive Expr.SameLambdaPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameLambdaPrefix 0 left right
  | cons : Expr.SameLambdaPrefix n left right →
      Expr.SameLambdaPrefix (n + 1)
        (.lam name dom left bi) (.lam name dom right bi)

/-- A forall telescope and a lambda telescope have the same binder domains. It lets the
domain translations of a checked forall be reused for the eta-expanded lambda over the
same local declarations. -/
inductive Expr.SameForallLambdaPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameForallLambdaPrefix 0 forallBody lambdaBody
  | cons : Expr.SameForallLambdaPrefix n forallBody lambdaBody →
      Expr.SameForallLambdaPrefix (n + 1)
        (.forallE name dom forallBody bi) (.lam name dom lambdaBody bi)

theorem Expr.SameForallLambdaPrefix.abstract1
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody)
    (fv : FVarId) (k : Nat := 0) :
    Expr.SameForallLambdaPrefix n
      (forallBody.abstract1 fv k) (lambdaBody.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameForallLambdaPrefix.abstractN
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.SameForallLambdaPrefix n
      (forallBody.abstractN fvs k) (lambdaBody.abstractN fvs k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstractN]
    exact .cons (ih (k + 1))

theorem Expr.SameForallLambdaPrefix.abstractList
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameForallLambdaPrefix n
      (forallBody.abstractList fvars k) (lambdaBody.abstractList fvars k) := by
  induction fvars generalizing forallBody lambdaBody k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

theorem Expr.SameLambdaPrefix.symm
    (H : Expr.SameLambdaPrefix n left right) :
    Expr.SameLambdaPrefix n right left := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem Expr.SameLambdaPrefix.abstract1
    (H : Expr.SameLambdaPrefix n left right) (fv : FVarId) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.abstract1 fv k) (right.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameLambdaPrefix.abstractN
    (H : Expr.SameLambdaPrefix n left right) (fvs : List FVarId) (k : Nat := 0) :
    Expr.SameLambdaPrefix n (left.abstractN fvs k) (right.abstractN fvs k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstractN]
    exact .cons (ih (k + 1))

theorem Expr.SameLambdaPrefix.abstractList
    (H : Expr.SameLambdaPrefix n left right)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.abstractList fvars k) (right.abstractList fvars k) := by
  induction fvars generalizing left right k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Substituting the same outer placeholder into two expressions preserves
their literal common lambda prefix.  Binder domains are transformed
identically; only the unrestricted residuals may differ. -/
theorem Expr.SameLambdaPrefix.instantiate1'
    (H : Expr.SameLambdaPrefix n left right)
    (value : Expr) (k : Nat := 0) :
    Expr.SameLambdaPrefix n
      (left.instantiate1' value k) (right.instantiate1' value k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
      simp only [Expr.instantiate1']
      exact .cons (ih (k + 1))

/-- Outermost specialization of `Expr.SameLambdaPrefix.instantiate1'`. -/
theorem Expr.SameLambdaPrefix.instantiate1
    (H : Expr.SameLambdaPrefix n left right) (value : Expr) :
    Expr.SameLambdaPrefix n
      (left.instantiate1 value) (right.instantiate1 value) := by
  simpa [Expr.instantiate1_eq] using H.instantiate1' value 0

theorem Expr.LambdaTelescope.trans
    (Houter : Expr.LambdaTelescope outer outerArity middle)
    (Hinner : Expr.LambdaTelescope middle innerArity result) :
    Expr.LambdaTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.LambdaTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

/-- A concrete lambda expression and arity determine its telescope residual. -/
theorem Expr.LambdaTelescope.result_eq
    (Hleft : Expr.LambdaTelescope outer arity left)
    (Hright : Expr.LambdaTelescope outer arity right) : left = right := by
  induction Hleft generalizing right with
  | nil => cases Hright; rfl
  | cons Hleft ih =>
      cases Hright with
      | cons Hright => exact ih Hright

/-- Instantiating an outer loose variable preserves a concrete lambda
telescope.  In the residual the substitution depth is shifted past every
leading binder, as when a closed recursive-call template is instantiated. -/
theorem Expr.LambdaTelescope.instantiate1'
    (H : Expr.LambdaTelescope outer arity result)
    (value : Expr) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.instantiate1' value k) arity
      (result.instantiate1' value (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
      simp only [Expr.instantiate1']
      apply Expr.LambdaTelescope.cons
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Specialization of `Expr.LambdaTelescope.instantiate1'` at the outermost
substitution depth. -/
theorem Expr.LambdaTelescope.instantiate1
    (H : Expr.LambdaTelescope outer arity result) (value : Expr) :
    Expr.LambdaTelescope (outer.instantiate1 value) arity
      (result.instantiate1' value arity) := by
  simpa [Expr.instantiate1_eq] using H.instantiate1' value 0

theorem Expr.LambdaTelescope.abstract1
    (H : Expr.LambdaTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.LambdaTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.LambdaTelescope.abstractList
    (H : Expr.LambdaTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

theorem Expr.LambdaTelescope.abstractN
    (H : Expr.LambdaTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstractN fvs k) arity
      (result.abstractN fvs (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstractN]
    apply Expr.LambdaTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- A lambda telescope whose binder domains avoid a selected set of
constants.  The residual body is intentionally unrestricted: generated
recursive calls contain the newly installed recursor in that position. -/
inductive Expr.AvoidingLambdaTelescope (names : List Name) :
    Expr → Nat → Expr → Prop
  | nil (body : Expr) : AvoidingLambdaTelescope names body 0 body
  | cons : dom.AvoidsConsts names →
      AvoidingLambdaTelescope names body arity result →
      AvoidingLambdaTelescope names (.lam name dom body bi) (arity + 1)
        result

theorem Expr.AvoidingLambdaTelescope.trans
    (Houter : Expr.AvoidingLambdaTelescope names outer outerArity middle)
    (Hinner : Expr.AvoidingLambdaTelescope names middle innerArity result) :
    Expr.AvoidingLambdaTelescope names outer (outerArity + innerArity)
      result := by
  induction Houter with
  | nil => simpa using Hinner
  | cons hdom Houter ih =>
    simpa [Nat.add_assoc, Nat.add_comm innerArity 1] using
      Expr.AvoidingLambdaTelescope.cons hdom (ih Hinner)

end VerifyInductive
end Lean4Lean
