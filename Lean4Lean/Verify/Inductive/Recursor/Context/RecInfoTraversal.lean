import Lean4Lean.Verify.Inductive.Constructor.Normalization

/-! Support for the proofs about the executable traversal in `mkRecInfos`: the
proof-side record of the recursive fields selected by `loopCtorArgs`
(`RecursiveFieldDomain`, `RecursiveFieldSelections`), the common-parameter prefix
of a constructor type that `loopCtorArgs` follows (`ParameterPrefix`,
`ParameterSegment`), and small lemmas about the reader monad and array updates
used by the traversal proofs. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursiveFieldDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env decl.uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursiveFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursiveFieldDomain env decl) → Prop
  | nil : RecursiveFieldSelections env decl #[] #[] []
  | nonrecursive : RecursiveFieldSelections env decl bu u fields →
      RecursiveFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursiveFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursiveFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursiveFieldSelections.selectedSublist
    (H : RecursiveFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]


/-- Exact concrete common-parameter prefix used by recursor generation.
The relation is intentionally separate from field classification: agreement
of these substitutions with the abstract parameter telescope is established
during constructor checking. -/
inductive ParameterPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → ParameterPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      ParameterPrefix stats (i + 1) (body.instantiate1 param) tail →
      ParameterPrefix stats i (.forallE name dom body bi) tail

/-- Replaying the cached parameter prefix is deterministic. -/
theorem ParameterPrefix.tail_eq
    (Hleft : ParameterPrefix stats i source left)
    (Hright : ParameterPrefix stats i source right) : left = right := by
  induction Hleft with
  | done hi =>
    cases Hright with
    | done => rfl
    | step hparam _ =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
  | @step i param body left dom name bi hparam Hleft ih =>
    cases Hright with
    | done hi =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
    | step hparam' Hright =>
      have heq : param = _ := Option.some.inj (hparam.symm.trans hparam')
      subst_vars
      exact ih Hright

/-- A pure forall spine of the cached-parameter tail extends to the closed
constructor type: the instantiated parameters are free variables, which cannot
alter the binder structure. -/
theorem ParameterPrefix.forallSpine
    (H : ParameterPrefix stats i source tail)
    (hfv : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv)
    (hspine : Expr.ForallSpine tail k) :
    Expr.ForallSpine source (stats.params.size - i + k) := by
  induction H with
  | done hi =>
    subst hi
    simpa using hspine
  | @step i param body tail name dom bi hparam _ ih =>
    have hi : i < stats.params.size :=
      (Array.getElem?_eq_some_iff.mp hparam).1
    rcases hfv param (Array.mem_of_getElem? hparam) with ⟨fv, rfl⟩
    have hbody := ih hspine
    rw [Expr.instantiate1_eq] at hbody
    have hbody' := Expr.ForallSpine.of_instantiate1'_fvar hbody
    have heq : stats.params.size - i + k =
        stats.params.size - (i + 1) + k + 1 := by omega
    rw [heq]
    exact .step hbody'

/-- A partially instantiated common-parameter prefix.  Constructor checking
builds this left-to-right; when `stop = stats.params.size`, it is exactly the
complete prefix replay required by recursor generation. -/
inductive ParameterSegment (stats : AddInductive.InductiveStats) :
    Nat → Nat → Expr → Expr → Prop
  | done : ParameterSegment stats i i source source
  | step {i stop : Nat} {param body tail dom : Expr}
      {name : Name} {bi : BinderInfo} :
      stats.params[i]? = some param →
      ParameterSegment stats (i + 1) stop
        (body.instantiate1 param) tail →
      ParameterSegment stats i stop (.forallE name dom body bi) tail

theorem ParameterSegment.trans
    (H₁ : ParameterSegment stats start middle source current)
    (H₂ : ParameterSegment stats middle stop current tail) :
    ParameterSegment stats start stop source tail := by
  induction H₁ with
  | done => exact H₂
  | step hparam _ ih => exact .step hparam (ih H₂)

theorem ParameterSegment.push
    {body param dom : Expr} {name : Name} {bi : BinderInfo}
    (H : ParameterSegment stats start i source
      (.forallE name dom body bi))
    (hparam : stats.params[i]? = some param) :
    ParameterSegment stats start (i + 1) source
      (body.instantiate1 param) := by
  exact H.trans (.step hparam .done)

theorem ParameterSegment.complete
    (H : ParameterSegment stats start stop source tail)
    (hstop : stop = stats.params.size) :
    ParameterPrefix stats start source tail := by
  induction H with
  | done => exact .done hstop
  | step hparam _ ih => exact .step hparam (ih hstop)

namespace mkRecInfos.loopCtorArgs.loop

/-- `loopCtorArgs.loop` follows a certified common-parameter prefix without
changing either accumulator, then delegates to the supplied tail proof. Fuel
exhaustion is harmless because it cannot return successfully. -/
theorem followsParamPrefix {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t tail : Expr} {i : Nat} {bu u : Array Expr}
    {c : AddInductive.Context} {Q : α → Prop}
    (hprefix : ParameterPrefix stats i t tail)
    (Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size bu u fuel c).WF Q) :
    ∀ fuel, (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  intro fuel
  induction fuel generalizing t i with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases hprefix with
    | done hi =>
      subst i
      exact Htail (fuel + 1)
    | @step i param body tail name dom bi hparam hprefix =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop, hparam]
      exact ih hprefix

end mkRecInfos.loopCtorArgs.loop

/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[], ruleTemplates := #[] } =
    { b with minors := #[], ruleTemplates := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

end mkRecInfos.loopInd2

end VerifyInductive
end Lean4Lean
