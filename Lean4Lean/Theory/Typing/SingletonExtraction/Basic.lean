import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.CaseMajorDomain
import Lean4Lean.Theory.Inductive.CaseProjections

/-! # Extraction of singleton proof fields along type casts

For a large-eliminating inductive proposition with one constructor, every data
field occurs literally as an index ("singleton elimination"), so the data of a
proof `m : I ps idx` can be read from `idx`. A proof field is extracted from `m`
itself by eliminating into `Prop`. The motive must be well typed at *generic*
indices `is'`, where the index slot of a data field has type `IdxTy(is')`, which in
general is not the field's declared type `A(…)` (the strengthening countermodel, section 5.1
of the design notes). The motive therefore abstracts, for each earlier
field, either an equation between the two *types* (data field) or a proof (proof field),
and reads each data field through a cast along its equation:

```text
cast telescope, field i < j:
  data i (slot k): e_i : @Eq (Sort u_i) IdxTy_k(ps, is'_<k) A_i(ps, σ_<i)
                   σ_i := typeCast u_i _ _ e_i is'_k
  proof i:         z_i : A_i(ps, σ_<i)
                   σ_i := z_i
target:            A_j(ps, σ_<j)
```

In the constructor branch every equation relates definitionally equal types, so
each cast computes by K (`IsDefEq.typeCast_refl`); at an aligned occurrence the
equations are proved by `Eq.refl`.

This file contains the syntax (`SingletonLayout`, `SingletonLayout.tel`) and its behaviour under
substitution. All telescopes are closed: `fields[i]` is scoped over the parameters
and the earlier fields, `indices[k]` over the parameters and the earlier indices.
The construction is parametric in the *providers*: the parameter arguments `pa` and
the index arguments `ia`, given at the base of the cast telescope and lifted beneath
its binders. The generic motive, the constructor branch and an actual occurrence are
the three instances. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

namespace VExpr

theorem instOuter_subst_closed (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length)
    (τ : Subst) : (X.instOuter args).subst τ = X.instOuter (args.map (fun x : VExpr => x.subst τ)) := by
  simp only [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map]

@[simp] theorem eqApp_subst (w α a b) (τ : Subst) :
    (eqApp w α a b).subst τ = eqApp w (α.subst τ) (a.subst τ) (b.subst τ) := rfl

end VExpr

/-- Pure syntax of a singleton family's field and index telescopes. -/
structure SingletonLayout where
  /-- `fields[i]` is scoped over `params ++ fields.take i`. -/
  fields : List VExpr
  /-- `indices[k]` is scoped over `params ++ indices.take k`. -/
  indices : List VExpr
  /-- `slot[i] = some k`: field `i` is data and occurs literally as index `k`;
  `none`: field `i` is a proof. -/
  slot : List (Option Nat)
  /-- The sort of each data field (unused for proof fields). -/
  sorts : List VLevel

namespace SingletonLayout
variable (S : SingletonLayout)

/-- One step of the cast telescope at depth `i` (the number of cast binders already
opened), given the substitution `σ` for the first `i` fields at that depth. Returns the
new binder domain and the value of field `i` beneath the new binder. -/
def step (pa ia : List VExpr) (i : Nat) (σ : List VExpr) : VExpr × VExpr :=
  let pai := pa.map (fun x : VExpr => x.liftN i)
  let Y := (S.fields.getD i default).instOuter (pai ++ σ)
  match S.slot.getD i none with
  | some k =>
    let X := (S.indices.getD k default).instOuter (pai ++ (ia.take k).map (fun x : VExpr => x.liftN i))
    let u := S.sorts.getD i .zero
    (VExpr.eqApp (.succ u) (.sort u) X Y,
      VExpr.typeCast u X.lift Y.lift (.bvar 0) ((ia.getD k default).liftN (i + 1)))
  | none => (Y, .bvar 0)

/-- The cast telescope for the first `i` fields: its domains (the `l`-th scoped at
depth `l`) and the substitution for those fields at depth `i`. -/
def tel (pa ia : List VExpr) : Nat → List VExpr × List VExpr
  | 0 => ([], [])
  | i + 1 =>
    let (doms, σ) := tel pa ia i
    let (dom, val) := S.step pa ia i σ
    (doms ++ [dom], σ.map (·.lift) ++ [val])

/-- The target of proof field `j`: its declared type at the cast data. -/
def target (pa ia : List VExpr) (j : Nat) : VExpr :=
  (S.fields.getD j default).instOuter (pa.map (·.liftN j) ++ (S.tel pa ia j).2)

theorem tel_length (pa ia : List VExpr) (i : Nat) :
    (S.tel pa ia i).1.length = i ∧ (S.tel pa ia i).2.length = i := by
  induction i with
  | zero => simp [tel]
  | succ i ih => simp [tel, ih]

/-- Scoping data of a cast specification over `P` parameters. -/
structure Scoped (P : Nat) : Prop where
  fields : ∀ i (h : i < S.fields.length), (S.fields[i]).ClosedN (P + i)
  indices : ∀ k (h : k < S.indices.length), (S.indices[k]).ClosedN (P + k)
  slot_lt : ∀ i k, S.slot.getD i none = some k → k < S.indices.length

theorem Scoped.fields_getD {S : SingletonLayout} (H : S.Scoped P) (i : Nat) :
    (S.fields.getD i default).ClosedN (P + i) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < S.fields.length
  · simpa [List.getElem?_eq_getElem hi] using H.fields i hi
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem Scoped.indices_getD {S : SingletonLayout} (H : S.Scoped P) (k : Nat) :
    (S.indices.getD k default).ClosedN (P + k) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < S.indices.length
  · simpa [List.getElem?_eq_getElem hk] using H.indices k hk
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hk)]

end SingletonLayout

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem getD_of_lt {l : List α} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem _root_.Lean4Lean.VExpr.Subst.ofList_snoc_tail (args : List VExpr) (a : VExpr) :
    (VExpr.Subst.ofList (args ++ [a])).tail = VExpr.Subst.ofList args := by
  funext k
  simp only [VExpr.Subst.tail, VExpr.Subst.ofList, List.length_append, List.length_singleton]
  by_cases hk : k < args.length
  · rw [dif_pos (by omega), dif_pos hk, List.getElem_append_left (by omega)]
    congr 1; omega
  · rw [dif_neg (by omega), dif_neg hk]; congr 1; omega

theorem _root_.Lean4Lean.VExpr.Subst.ofList_snoc_head (args : List VExpr) (a : VExpr) :
    (VExpr.Subst.ofList (args ++ [a])).head = a := by
  simp [VExpr.Subst.head, VExpr.Subst.ofList]


end VEnv

namespace SingletonLayout
open VEnv
variable {env : VEnv} {U : Nat}

theorem bvarRange_split (P r : Nat) :
    bvarRange (P + r) (P + r) = bvarRange P (P + r) ++ bvarRange r r := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [bvarRange_length] at h1
    by_cases hj : j < P
    · rw [List.getElem_append_left (by simpa using hj), bvarRange_getElem _ _ _ h1,
        bvarRange_getElem _ _ _ hj]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hj), bvarRange_getElem _ _ _ h1]
      simp only [bvarRange_length]
      rw [bvarRange_getElem _ _ _ (by omega)]
      congr 1; omega

end SingletonLayout

/-- The syntax of a singleton family's elimination into `Prop`, at fixed universe levels:
the family and constructor heads (closed terms applied to parameters and indices), the
constructor's result indices (scoped over the parameters and fields), the eliminator head
specialized to motive universe zero, and how a minor premise is built from a motive and a
branch over the fields (for recursors this adds the unused induction hypotheses). -/
structure PropElim where
  family : VExpr
  ctor : VExpr
  ctorIndices : List VExpr
  elimHead : VExpr
  minorOf : VExpr → VExpr → VExpr

namespace PropElim
variable (S : SingletonLayout) (params : List VExpr) (E : PropElim)

/-- The major premise's type, scoped over the parameters and the indices. -/
def majorTy : VExpr :=
  VExpr.mkApps E.family
    (bvarRange params.length (params.length + S.indices.length) ++
      bvarRange S.indices.length S.indices.length)

/-- Providers of the generic motive: the parameters and indices beneath the major. -/
def genericPa : List VExpr :=
  bvarRange params.length (params.length + S.indices.length + 1)
def genericIa : List VExpr := bvarRange S.indices.length (S.indices.length + 1)

/-- Providers of the constructor branch: the parameters beneath the fields, and the
constructor's own indices. -/
def branchPa : List VExpr := bvarRange params.length (params.length + S.fields.length)

/-- The motive extracting proof field `j`, scoped over the parameters. -/
def motive (j : Nat) : VExpr :=
  VExpr.wrapLams (S.indices ++ [majorTy S params E])
    (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j))

/-- The branch returning field `j`, scoped over the parameters and the fields. -/
def branch (j : Nat) : VExpr :=
  VExpr.wrapLams (S.tel (branchPa S params) E.ctorIndices j).1 (.bvar (S.fields.length - 1))

/-- The closed extraction function for proof field `j`: a function of the parameters,
the indices, the major premise and the cast telescope. -/
def value (j : Nat) : VExpr :=
  VExpr.wrapLams (params ++ S.indices ++ [majorTy S params E])
    (VExpr.mkApps E.elimHead
      (genericPa S params ++
        [(motive S params E j).liftN (S.indices.length + 1),
          (E.minorOf (motive S params E j) (branch S params E j)).liftN (S.indices.length + 1)] ++
        bvarRange (S.indices.length + 1) (S.indices.length + 1)))

/-- The cast arguments (`.1`) and the reconstructed fields (`.2`) at an occurrence with
parameters `ps`, indices `idx` and major `m`. A data field is read from its index; the cast
argument for it is `Eq.refl` at the index's type. A proof field is the extraction function
applied to the occurrence and to the earlier cast arguments. -/
def occ (ps idx : List VExpr) (m : VExpr) : Nat → List VExpr × List VExpr
  | 0 => ([], [])
  | i + 1 =>
    let (t, c) := occ ps idx m i
    match S.slot.getD i none with
    | some k =>
      (t ++ [VExpr.eqReflApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero))
          ((S.indices.getD k default).instOuter (ps ++ idx.take k))],
        c ++ [idx.getD k default])
    | none =>
      (t ++ [VExpr.mkApps (value S params E i) (ps ++ idx ++ [m] ++ t)],
        c ++ [VExpr.mkApps (value S params E i) (ps ++ idx ++ [m] ++ t)])

theorem occ_length (ps idx : List VExpr) (m : VExpr) (i : Nat) :
    (occ S params E ps idx m i).1.length = i ∧ (occ S params E ps idx m i).2.length = i := by
  induction i with
  | zero => simp [occ]
  | succ i ih =>
    simp only [occ]
    split <;> simp [ih]

end PropElim
end Lean4Lean
