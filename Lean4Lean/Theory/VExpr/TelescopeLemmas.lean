import Lean4Lean.Theory.VExpr.Telescope

/-! # Dependent telescope syntax

Lifting, substitution, application spines, and telescope shape relations for the abstract
calculus. Existing `VerifyInductive` names are retained for compatibility with their consumers.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open scoped _root_.List

namespace VerifyInductive

/-- A dependent function type with exactly `arity` binders and a sort as its
final codomain.  Instantiating term variables preserves this shape because
universe levels do not depend on terms. -/
inductive VExpr.ForallAritySort : Nat → VExpr → Prop
  | zero (level : VLevel) : ForallAritySort 0 (.sort level)
  | succ (domain : VExpr) : ForallAritySort arity body →
      ForallAritySort (arity + 1) (.forallE domain body)

theorem VExpr.ForallAritySort.inst
    (H : ForallAritySort arity type) (arg : VExpr) (k : Nat := 0) :
    ForallAritySort arity (type.inst arg k) := by
  induction H generalizing k with
  | zero => exact .zero _
  | succ domain H ih =>
    simpa [VExpr.inst] using ForallAritySort.succ
      (domain.inst arg k) (ih (k + 1))

theorem VExpr.ForallAritySort.instL
    (H : ForallAritySort arity type) (levels : List VLevel) :
    ForallAritySort arity (type.instL levels) := by
  induction H with
  | zero => exact .zero _
  | succ domain H ih =>
    simpa [VExpr.instL] using ForallAritySort.succ
      (domain.instL levels) ih

theorem VExpr.ForallAritySort.wrapForalls
    (domains : List VExpr) (level : VLevel) :
    ForallAritySort domains.length
      (VExpr.wrapForalls domains (.sort level)) := by
  induction domains with
  | nil => exact .zero level
  | cons domain domains ih =>
    simpa [VExpr.wrapForalls] using ForallAritySort.succ domain ih

/-- The first `n` domains of a wrapped telescope are syntactically unique.
The residual bodies may differ, and the longer presentation may retain an
arbitrary suffix after the compared prefix. -/
theorem VExpr.wrapForalls_prefix_domains_eq
    (hleft : left.length = n) (hright : right.length = n)
    (H : VExpr.wrapForalls left leftBody =
      VExpr.wrapForalls (right ++ suffix) rightBody) :
    left = right := by
  have htake := congrArg (fun type => type.takeForalls n) H
  have htakeLeft :
      (VExpr.wrapForalls left leftBody).takeForalls n = some (left, leftBody) := by
    rw [← hleft]
    exact VExpr.takeForalls_wrapForalls left leftBody
  have htakeRight :
      (VExpr.wrapForalls (right ++ suffix) rightBody).takeForalls n =
        some (right, VExpr.wrapForalls suffix rightBody) := by
    rw [← hright]
    exact VExpr.takeForalls_wrapForalls_append right suffix rightBody
  rw [htakeLeft, htakeRight] at htake
  exact congrArg Prod.fst (Option.some.inj htake)

/-- Wrapping the same dependent domain list on both sides is injective in
the residual body. -/
theorem VExpr.wrapForalls_left_cancel
    (domains : List VExpr)
    (H : VExpr.wrapForalls domains left =
      VExpr.wrapForalls domains right) :
    left = right := by
  induction domains with
  | nil => simpa [VExpr.wrapForalls] using H
  | cons domain domains ih =>
    simp only [VExpr.wrapForalls] at H
    injection H with _ hbody
    exact ih hbody

/-- Lift a recent context prefix over a block inserted immediately beneath
it, starting at cutoff `k` below the whole prefix.  The cutoff decreases as
the prefix is traversed from newest to oldest. -/
def liftContextPrefixAt (n k : Nat) : List VExpr → List VExpr
  | [] => []
  | domain :: domains =>
    domain.liftN n (k + domains.length) ::
      liftContextPrefixAt n k domains

def liftContextPrefix (n : Nat) (domains : List VExpr) : List VExpr :=
  liftContextPrefixAt n 0 domains

@[simp] theorem liftContextPrefixAt_length
    (n k : Nat) (domains : List VExpr) :
    (liftContextPrefixAt n k domains).length = domains.length := by
  induction domains with
  | nil => rfl
  | cons domain domains ih => simp [liftContextPrefixAt, ih]

@[simp] theorem liftContextPrefix_length
    (n : Nat) (domains : List VExpr) :
    (liftContextPrefix n domains).length = domains.length := by
  exact liftContextPrefixAt_length n 0 domains

theorem liftContextPrefixAt_append_singleton
    (n k : Nat) (domains : List VExpr) (domain : VExpr) :
    liftContextPrefixAt n k (domains ++ [domain]) =
      liftContextPrefixAt n (k + 1) domains ++ [domain.liftN n k] := by
  induction domains with
  | nil => simp [liftContextPrefixAt]
  | cons head domains ih =>
    simp [liftContextPrefixAt, ih, Nat.add_comm,
      Nat.add_left_comm]

/-- In outermost-to-innermost telescope order, the `j`th domain is weakened
below the `j` earlier binders. -/
theorem liftContextPrefixAt_reverse_getElem
    (n k : Nat) (domains : List VExpr) (j : Nat)
    (hj : j < domains.length) :
    ((liftContextPrefixAt n k domains.reverse).reverse)[j]! =
      domains[j]!.liftN n (k + j) := by
  induction domains generalizing k j with
  | nil => simp at hj
  | cons domain domains ih =>
    rw [List.reverse_cons, liftContextPrefixAt_append_singleton,
      List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append]
    cases j with
    | zero => simp [getElem!_pos]
    | succ j =>
      have hj' : j < domains.length := by simpa using hj
      simpa [getElem!_pos, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        ih (k := k + 1) (j := j) hj'

theorem liftContextPrefixAt_append
    (n k : Nat) (left right : List VExpr) :
    liftContextPrefixAt n k (left ++ right) =
      liftContextPrefixAt n (k + right.length) left ++
        liftContextPrefixAt n k right := by
  induction left with
  | nil => simp [liftContextPrefixAt]
  | cons domain left ih =>
    simp [liftContextPrefixAt, ih, Nat.add_assoc, Nat.add_comm]

theorem liftContextPrefixAt_reverse_append
    (n k : Nat) (outer inner : List VExpr) :
    (liftContextPrefixAt n k (outer ++ inner).reverse).reverse =
      (liftContextPrefixAt n k outer.reverse).reverse ++
        (liftContextPrefixAt n (k + outer.length) inner.reverse).reverse := by
  rw [List.reverse_append, liftContextPrefixAt_append,
    List.reverse_append]
  simp

theorem liftContextPrefixAt_reverse_append_take_left
    (n k : Nat) (outer inner : List VExpr) :
    ((liftContextPrefixAt n k (outer ++ inner).reverse).reverse).take
        outer.length =
      (liftContextPrefixAt n k outer.reverse).reverse := by
  rw [liftContextPrefixAt_reverse_append]
  simp

/-- In outermost-to-innermost telescope order, inserting beneath a combined
outer/inner prefix splits into the lifted outer domains followed by the
inner domains lifted at the outer cutoff. -/
theorem liftContextPrefix_reverse_append
    (n : Nat) (outer inner : List VExpr) :
    (liftContextPrefix n (outer ++ inner).reverse).reverse =
      (liftContextPrefix n outer.reverse).reverse ++
        (liftContextPrefixAt n outer.length inner.reverse).reverse := by
  unfold liftContextPrefix
  rw [List.reverse_append, liftContextPrefixAt_append,
    List.reverse_append]
  simp

/-- Lifting a dependent forall telescope is dual to lifting its reversed
context prefix. -/
theorem VExpr.liftN_wrapForalls
    (domains : List VExpr) (body : VExpr) (n k : Nat) :
    (VExpr.wrapForalls domains body).liftN n k =
      VExpr.wrapForalls
        ((liftContextPrefixAt n k domains.reverse).reverse)
        (body.liftN n (k + domains.length)) := by
  induction domains generalizing k with
  | nil => simp [VExpr.wrapForalls, liftContextPrefixAt]
  | cons domain domains ih =>
    change VExpr.forallE (domain.liftN n k)
      ((VExpr.wrapForalls domains body).liftN n (k + 1)) = _
    rw [ih,
      List.reverse_cons, liftContextPrefixAt_append_singleton]
    simp [VExpr.wrapForalls, Nat.add_comm,
      Nat.add_left_comm]

/-- An arbitrary free-variable lift preserves the number of leading forall
binders.  Unlike `liftN_wrapForalls`, the transformed dependent domains do
not have a useful closed formula for a general `Lift`, so this shape lemma
retains them existentially. -/
theorem VExpr.lift'_wrapForalls_shape
    (domains : List VExpr) (body : VExpr) (shift : Lift) :
    ∃ liftedDomains liftedBody,
      liftedDomains.length = domains.length ∧
      (VExpr.wrapForalls domains body).lift' shift =
        VExpr.wrapForalls liftedDomains liftedBody := by
  induction domains generalizing shift with
  | nil =>
      exact ⟨[], body.lift' shift, rfl, by simp [VExpr.wrapForalls]⟩
  | cons domain domains ih =>
      rcases ih shift.cons with
        ⟨liftedDomains, liftedBody, hlength, hshape⟩
      exact ⟨domain.lift' shift :: liftedDomains, liftedBody,
        by simp [hlength], by
          change VExpr.forallE (domain.lift' shift)
              ((VExpr.wrapForalls domains body).lift' shift.cons) =
            VExpr.forallE (domain.lift' shift)
              (VExpr.wrapForalls liftedDomains liftedBody)
          rw [hshape]⟩

/-- Canonical variables for a telescope, in source binder order. -/
def bvarSpine (n : Nat) : List VExpr :=
  (List.range n).reverse.map .bvar

@[simp] theorem bvarSpine_zero : bvarSpine 0 = [] :=
  rfl

theorem bvarSpine_eq_ofFn (n : Nat) :
    bvarSpine n =
      List.ofFn fun i : Fin n => VExpr.bvar (n - 1 - i) := by
  apply List.ext_getElem
  · simp [bvarSpine]
  · intro i hleft hright
    simp [bvarSpine]

theorem bvarSpine_succ_cons (n : Nat) :
    bvarSpine (n + 1) =
      .bvar n :: bvarSpine n := by
  simp [bvarSpine, List.range_succ]

/-- Split the bound-variable spine of a telescope into an older applied initial block,
weakened below the still-open suffix, followed by the suffix variables. -/
theorem bvarSpine_add (initialCount suffixCount : Nat) :
    bvarSpine (initialCount + suffixCount) =
      (bvarSpine initialCount).map
          (fun arg => arg.liftN suffixCount 0) ++
        bvarSpine suffixCount := by
  induction initialCount with
  | zero => simp
  | succ initialCount ih =>
    rw [show (initialCount + 1) + suffixCount =
        (initialCount + suffixCount) + 1 by omega,
      bvarSpine_succ_cons,
      bvarSpine_succ_cons, List.map_cons, ih]
    simp [VExpr.liftN]

theorem VExpr.liftN_mkApps
    (fn : VExpr) (args : List VExpr) (n k : Nat) :
    (VExpr.mkApps fn args).liftN n k =
      VExpr.mkApps (fn.liftN n k) (args.map fun arg => arg.liftN n k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simpa [VExpr.mkApps, VExpr.liftN] using ih (.app fn arg)

/-- Applying the full bound-variable spine factors through the bound-variable
application of any older initial block, weakened below the remaining suffix. -/
theorem VExpr.mkApps_bvarSpine_add
    (fn : VExpr) (initialCount suffixCount : Nat) :
    VExpr.mkApps (fn.liftN (initialCount + suffixCount) 0)
        (bvarSpine (initialCount + suffixCount)) =
      VExpr.mkApps
        ((VExpr.mkApps (fn.liftN initialCount 0)
          (bvarSpine initialCount)).liftN suffixCount 0)
        (bvarSpine suffixCount) := by
  have hinitialApp :
      VExpr.mkApps (fn.liftN (initialCount + suffixCount) 0)
          ((bvarSpine initialCount).map
            (fun arg => arg.liftN suffixCount 0)) =
        (VExpr.mkApps (fn.liftN initialCount 0)
          (bvarSpine initialCount)).liftN suffixCount 0 := by
    rw [VExpr.liftN_mkApps]
    simp [VExpr.liftN_liftN]
  rw [bvarSpine_add]
  rw [VExpr.mkApps_append, hinitialApp]

/-- The concrete owner-result spine numbers the index variables followed by
the major exactly as the bound-variable spine of one combined telescope. -/
theorem concreteRecursorResultArgs_eq_bvarSpine (numIndices : Nat) :
    ((List.range numIndices).reverse.map fun index =>
        VExpr.bvar (index + 1)) ++ [.bvar 0] =
      bvarSpine (numIndices + 1) := by
  induction numIndices with
  | zero => rfl
  | succ numIndices ih =>
    rw [List.range_succ, List.reverse_append, List.map_append]
    simpa [bvarSpine_succ_cons, List.append_assoc] using
      congrArg (VExpr.bvar (numIndices + 1) :: ·) ih

@[simp] theorem bvarSpine_liftN_at_length
    (n shift : Nat) :
    (bvarSpine n).map (fun arg => arg.liftN shift n) =
      bvarSpine n := by
  rw [bvarSpine_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_lt (by omega)]

theorem bvarSpine_liftN_comp
    (n inner outer : Nat) :
    ((bvarSpine n).map (fun arg => arg.liftN inner 0)).map
        (fun arg => arg.liftN outer inner) =
      (bvarSpine n).map
        (fun arg => arg.liftN (inner + outer) 0) := by
  rw [bvarSpine_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_base, liftVar_le (by omega), liftVar_base]
    congr 1
    omega

/-- Weakening the bound-variable spine of an outer telescope below an inner
block gives the direct de Bruijn numbering in the combined context. -/
theorem bvarSpine_liftN_zero_eq_ofFn
    (outer inner : Nat) :
    (bvarSpine outer).map
        (fun arg => arg.liftN inner 0) =
      List.ofFn fun i : Fin outer =>
        VExpr.bvar (outer + inner - 1 - i) := by
  rw [bvarSpine_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < outer := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.liftN]
    rw [liftVar_base]
    congr 1
    omega

/-- Two function types expose the same dependent domains while permitting
different residual result types.  This is the exact relation needed to use
a fully typed motive application as the argument certificate for a recursor
prefix whose result inhabits that motive application. -/
inductive SameTelescopeDomains : Nat → VExpr → VExpr → Prop
  | zero (left right : VExpr) : SameTelescopeDomains 0 left right
  | succ (domain left right : VExpr) {arity : Nat} :
      SameTelescopeDomains arity left right →
      SameTelescopeDomains (arity + 1)
        (.forallE domain left) (.forallE domain right)

/-- Two types expose the same number of forall binders, without requiring
their dependent domains to be literally identical.  This is the shape
relation used when an installed constructor parameter telescope is only
definitionally equal to the corresponding family telescope. -/
inductive SameTelescopeArity : Nat → VExpr → VExpr → Prop
  | zero (left right : VExpr) : SameTelescopeArity 0 left right
  | succ (leftDomain rightDomain left right : VExpr) {arity : Nat} :
      SameTelescopeArity arity left right →
      SameTelescopeArity (arity + 1)
        (.forallE leftDomain left) (.forallE rightDomain right)

theorem SameTelescopeArity.instN
    (H : SameTelescopeArity arity left right)
    (value : VExpr) (k : Nat) :
    SameTelescopeArity arity (left.inst value k) (right.inst value k) := by
  induction H generalizing k with
  | zero => exact .zero _ _
  | @succ leftDomain rightDomain left right arity H ih =>
      apply SameTelescopeArity.succ
      simpa [VExpr.inst] using ih (k + 1)

theorem SameTelescopeArity.wrapForalls
    (leftDomains rightDomains : List VExpr)
    (hlen : leftDomains.length = rightDomains.length)
    (left right : VExpr) :
    SameTelescopeArity leftDomains.length
      (VExpr.wrapForalls leftDomains left)
      (VExpr.wrapForalls rightDomains right) := by
  induction leftDomains generalizing rightDomains with
  | nil =>
    have hright : rightDomains = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst rightDomains
    exact .zero _ _
  | cons leftDomain leftDomains ih =>
    cases rightDomains with
    | nil => simp at hlen
    | cons rightDomain rightDomains =>
      apply SameTelescopeArity.succ
      exact ih rightDomains (by simpa using Nat.succ.inj hlen)

theorem SameTelescopeDomains.wrapForalls
    (domains : List VExpr) (left right : VExpr) :
    SameTelescopeDomains domains.length
      (VExpr.wrapForalls domains left)
      (VExpr.wrapForalls domains right) := by
  induction domains with
  | nil => exact .zero _ _
  | cons domain domains ih =>
    exact .succ domain _ _ ih

/-- Simultaneous substitution preserves a shared dependent-domain spine. -/
theorem SameTelescopeDomains.instN
    (H : SameTelescopeDomains arity left right)
    (value : VExpr) (k : Nat) :
    SameTelescopeDomains arity (left.inst value k) (right.inst value k) := by
  induction H generalizing k with
  | zero => exact .zero _ _
  | @succ domain left right arity H ih =>
    apply SameTelescopeDomains.succ
    simpa [VExpr.inst] using ih (k + 1)

/-- Consume a syntactic forall telescope with the supplied arguments and
return its instantiated residual type.  The fallback branch is irrelevant
for typed uses but keeps the operation total. -/
def VExpr.applyForallType : VExpr → List VExpr → VExpr
  | type, [] => type
  | .forallE _ body, arg :: args => applyForallType (body.inst arg) args
  | type, _ :: _ => type

def VExpr.instForallDomains : List VExpr → VExpr → Nat → List VExpr
  | [], _, _ => []
  | domain :: domains, arg, k =>
      domain.inst arg k :: instForallDomains domains arg (k + 1)

@[simp] theorem VExpr.instForallDomains_length :
    (VExpr.instForallDomains domains arg k).length = domains.length := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
    simp [VExpr.instForallDomains, ih]

theorem VExpr.inst_wrapForalls
    (domains : List VExpr) (body arg : VExpr) (k : Nat) :
    (VExpr.wrapForalls domains body).inst arg k =
      VExpr.wrapForalls (VExpr.instForallDomains domains arg k)
        (body.inst arg (k + domains.length)) := by
  induction domains generalizing k with
  | nil => simp [VExpr.wrapForalls, VExpr.instForallDomains]
  | cons domain domains ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons,
      VExpr.instForallDomains, VExpr.inst]
    congr 1
    change (VExpr.wrapForalls domains body).inst arg (k + 1) =
      VExpr.wrapForalls (VExpr.instForallDomains domains arg (k + 1))
        (body.inst arg (k + (domains.length + 1)))
    rw [show k + (domains.length + 1) = k + 1 + domains.length by omega]
    exact ih (k + 1)

/-- Place independently typed closed domains into one dependent telescope.
The domain at chronological position `i` is weakened below the `i` earlier
binders, so substituting those binders recovers its original closed type. -/
def VExpr.liftClosedDomains : List VExpr → Nat → List VExpr
  | [], _ => []
  | domain :: domains, depth =>
      domain.liftN depth 0 :: liftClosedDomains domains (depth + 1)

@[simp] theorem VExpr.liftClosedDomains_length :
    (VExpr.liftClosedDomains domains depth).length = domains.length := by
  induction domains generalizing depth with
  | nil => rfl
  | cons domain domains ih =>
    simp [VExpr.liftClosedDomains, ih]

theorem VExpr.liftClosedDomains_getElem
    (domains : List VExpr) (depth i : Nat)
    (hi : i < domains.length) :
    (VExpr.liftClosedDomains domains depth)[i]'(by simpa using hi) =
      domains[i].liftN (depth + i) 0 := by
  induction domains generalizing depth i with
  | nil => simp at hi
  | cons domain domains ih =>
    cases i with
    | zero => simp [VExpr.liftClosedDomains]
    | succ i =>
      have hi' : i < domains.length := by simpa using hi
      simpa [VExpr.liftClosedDomains, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (depth + 1) i hi'

/-- Instantiating the next binder cancels one layer of the systematic
weakening in every later independent domain. -/
theorem VExpr.instForallDomains_liftClosedDomains_succ
    (domains : List VExpr) (arg : VExpr) (k : Nat) :
    VExpr.instForallDomains
        (VExpr.liftClosedDomains domains (k + 1)) arg k =
      VExpr.liftClosedDomains domains k := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
    simp only [VExpr.liftClosedDomains, VExpr.instForallDomains]
    have hhead : (domain.liftN (k + 1) 0).inst arg k =
        domain.liftN k 0 := by
      rw [show domain.liftN (k + 1) 0 =
          (domain.liftN k 0).liftN 1 k by
        simpa [Nat.add_comm] using
          (VExpr.liftN'_liftN_lo domain 1 k).symm]
      exact VExpr.inst_liftN (domain.liftN k 0) arg
    rw [hhead]
    congr 1
    simpa [Nat.add_assoc] using ih (k + 1)

theorem VExpr.inst_mkApps
    (fn arg : VExpr) (args : List VExpr) (k : Nat) :
    (VExpr.mkApps fn args).inst arg k =
      VExpr.mkApps (fn.inst arg k) (args.map fun e => e.inst arg k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons head tail ih =>
    simpa [VExpr.mkApps, VExpr.inst] using ih (.app fn head)

@[simp] theorem bvarSpine_inst_at_length
    (n : Nat) (arg : VExpr) :
    (bvarSpine n).map (fun e => e.inst arg n) =
      bvarSpine n := by
  rw [bvarSpine_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn, VExpr.inst,
      VExpr.instVar]
    rw [if_pos (by omega)]

theorem VExpr.inst_canonicalResult
    (fn arg : VExpr) (n : Nat) :
    (VExpr.mkApps (fn.liftN (n + 1) 0)
        (bvarSpine (n + 1))).inst arg n =
      VExpr.mkApps ((VExpr.app fn arg).liftN n 0)
        (bvarSpine n) := by
  rw [VExpr.inst_mkApps, bvarSpine_succ_cons,
    List.map_cons, bvarSpine_inst_at_length,
    VExpr.inst_liftN_lo]
  simp [VExpr.mkApps, VExpr.inst, VExpr.instVar, VExpr.liftN]

/-- Opening a bound-variable result spine and substituting one argument for each
telescope binder produces the same application with those concrete
arguments. -/
theorem VExpr.applyForallType_wrapForalls_bvarSpine
    (domains args : List VExpr) (fn : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains
          (VExpr.mkApps (fn.liftN domains.length 0)
            (bvarSpine domains.length))) args =
      VExpr.mkApps fn args := by
  have go : ∀ n (domains args : List VExpr) (fn : VExpr),
      domains.length = n → args.length = n →
      VExpr.applyForallType
          (VExpr.wrapForalls domains
            (VExpr.mkApps (fn.liftN n 0)
              (bvarSpine n))) args =
        VExpr.mkApps fn args := by
    intro n
    induction n with
    | zero =>
      intro domains args fn hdomains hargs
      have hdomains' : domains = [] :=
        List.eq_nil_of_length_eq_zero hdomains
      have hargs' : args = [] :=
        List.eq_nil_of_length_eq_zero hargs
      subst domains
      subst args
      simp [VExpr.applyForallType, VExpr.wrapForalls, VExpr.mkApps]
    | succ n ih =>
      intro domains args fn hdomains hargs
      cases domains with
      | nil => simp at hdomains
      | cons domain domains =>
        cases args with
        | nil => simp at hargs
        | cons arg args =>
          have hdomainsTail : domains.length = n := by
            simpa using Nat.succ.inj hdomains
          have hargsTail : args.length = n := by
            simpa using Nat.succ.inj hargs
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (VExpr.mkApps (fn.liftN (n + 1) 0)
                (bvarSpine (n + 1)))).inst arg) args =
            VExpr.mkApps fn (arg :: args)
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [hdomainsTail]
          rw [VExpr.inst_canonicalResult]
          exact ih (VExpr.instForallDomains domains arg 0) args
            (VExpr.app fn arg) (by simpa using hdomainsTail) hargsTail
  exact go domains.length domains args fn rfl hlength

/-- Parallel telescope relation between an inductive family and its motive.
Both functions consume the same dependent domains.  Once all domains have
been consumed, the motive expects an inhabitant of the corresponding family
application and returns the selected elimination sort. -/
inductive RecursorMotiveTelescope (resultLevel : VLevel) :
    Nat → VExpr → VExpr → VExpr → Prop
  | zero (family familyType : VExpr) :
      RecursorMotiveTelescope resultLevel 0 family familyType
        (.forallE family (.sort resultLevel))
  | succ (family domain familyType motiveType : VExpr) {arity : Nat} :
      RecursorMotiveTelescope resultLevel arity
        (.app (family.liftN 1 0) (.bvar 0)) familyType motiveType →
      RecursorMotiveTelescope resultLevel (arity + 1) family
        (.forallE domain familyType) (.forallE domain motiveType)

/-- Closing the same dependent domains over a family result and over the
corresponding family-major proposition produces a parallel motive
telescope. -/
theorem RecursorMotiveTelescope.wrapForalls
    (domains : List VExpr) (family familyResult : VExpr)
    (resultLevel : VLevel) :
    RecursorMotiveTelescope resultLevel domains.length family
      (VExpr.wrapForalls domains familyResult)
      (VExpr.wrapForalls domains
        (.forallE
          (VExpr.mkApps (family.liftN domains.length 0)
            (bvarSpine domains.length))
          (.sort resultLevel))) := by
  induction domains generalizing family with
  | nil =>
    simpa [VExpr.wrapForalls, VExpr.mkApps] using
      (RecursorMotiveTelescope.zero (resultLevel := resultLevel)
        family familyResult)
  | cons domain domains ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.wrapForalls, bvarSpine_succ_cons,
      VExpr.mkApps, VExpr.liftN, VExpr.liftN_liftN, Nat.add_comm] using
      ih (.app (family.liftN 1 0) (.bvar 0))

/-- Weakening all three expressions preserves a parallel motive telescope. -/
theorem RecursorMotiveTelescope.liftN
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (n k : Nat) :
    RecursorMotiveTelescope resultLevel arity
      (family.liftN n k) (familyType.liftN n k)
      (motiveType.liftN n k) := by
  induction H generalizing k with
  | zero => simp [VExpr.liftN, RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.liftN, VExpr.lift, VExpr.lift_liftN'] using ih (k + 1)

/-- Weakening a parallel motive telescope by an arbitrary context embedding
preserves the relation.  The embedding is extended below each shared binder,
exactly as `VExpr.lift'` traverses a dependent forall. -/
theorem RecursorMotiveTelescope.lift'
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (shift : Lift) :
    RecursorMotiveTelescope resultLevel arity
      (family.lift' shift) (familyType.lift' shift)
      (motiveType.lift' shift) := by
  induction H generalizing shift with
  | zero => simp [RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
    apply RecursorMotiveTelescope.succ
    simpa [VExpr.liftN, VExpr.lift, VExpr.lift_eq_lift',
      ← VExpr.lift'_comp] using ih shift.cons

/-- Simultaneous term substitution preserves the parallel family/motive
telescope relation.  The explicit cutoff is needed under dependent binders. -/
theorem RecursorMotiveTelescope.instN
    (H : RecursorMotiveTelescope resultLevel arity family familyType
      motiveType) (value : VExpr) (k : Nat) :
    RecursorMotiveTelescope resultLevel arity
      (family.inst value k) (familyType.inst value k)
      (motiveType.inst value k) := by
  induction H generalizing k with
  | zero => simp [VExpr.inst, RecursorMotiveTelescope.zero]
  | @succ family domain familyType motiveType arity Htail ih =>
      apply RecursorMotiveTelescope.succ
      simpa [VExpr.inst, VExpr.lift, VExpr.lift_instN_lo] using
        ih (k + 1)

theorem VExpr.getAppFnArgs_mkApps
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs =
      let (head, prior) := fn.getAppFnArgs
      (head, prior ++ args) := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args from rfl, ih]
      simp [List.append_assoc]

@[simp] theorem VExpr.getAppFnArgs_mkApps_bvar
    (index : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar index) args).getAppFnArgs = (.bvar index, args) := by
  simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using
    VExpr.getAppFnArgs_mkApps (.bvar index) args

end VerifyInductive
end Lean4Lean
