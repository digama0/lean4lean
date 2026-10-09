import Lean4Lean.Theory.Typing.TypeChain

/-! # Declarative classes of the glued observation model

Classes of terms in a fixed *target context* `Δ` (section 4.1 of the design notes):

* `TyCls Δ A`: the type class of `A`, the terms related to `A` by a chain of sort-typed
  definitional equalities (`TypeChain`), together with `A` itself;
* `ElCls Δ D a`: the element class of `a` at a set `D` of types, the closure of `a` under
  definitional equalities typed at some member of `D`;
* `TypedElCls`: the element classes of typed terms.

The **collapse lemma** (`ElCls.collapse`) turns membership of an element class at a type
class `TyCls Δ X₀` into one definitional equality at `X₀`: every link is transported to
`X₀` along a chain (`TypeChain.defeqDF`) and links at one type compose by `trans`. This is
why classes are typed.

The model built on this file (`Obs.lean`, `Interp.lean`) uses valuations consisting of an
*anchor* substitution together with observation sets, and computes classes from the anchor.
Related anchors are pairs of definitionally equal substitutions (`Ctx.SubstEq`, with
`SubstEq.symm` and `SubstEq.right` below).

Sets are predicates (`VExpr → Prop`); this development does not use Mathlib. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Terms that differ only by `≈`-equivalent well-formed levels. Reflexive on every term
(the `refl` constructor), so it is closed under substitution. Classes are saturated by it: for typed terms this adds nothing
(`LvEq.defeq`), and it makes the observation interpretation invariant under level
equivalence structurally. -/
inductive LvEq (U : Nat) : VExpr → VExpr → Prop
  | refl : LvEq U e e
  | sort : l.WF U → l'.WF U → l ≈ l' → LvEq U (.sort l) (.sort l')
  | const : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    LvEq U (.const c ls) (.const c ls')
  | elim : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    LvEq U (.elim b o ls) (.elim b o ls')
  | app : LvEq U f f' → LvEq U a a' → LvEq U (.app f a) (.app f' a')
  | lam : LvEq U A A' → LvEq U t t' → LvEq U (.lam A t) (.lam A' t')
  | forallE : LvEq U A A' → LvEq U B B' → LvEq U (.forallE A B) (.forallE A' B')
  | proj : LvEq U e e' → LvEq U (.proj n i e) (.proj n i e')

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- A sort-typed definitional equality in `Δ`. -/
def TyLink (A B : VExpr) : Prop := ∃ u, env.IsDefEq U Δ A B (.sort u)

/-- One step of a type class: a sort-typed equality or a level variant. -/
def TyStep (A B : VExpr) : Prop := TyLink env U Δ A B ∨ LvEq U A B ∨ LvEq U B A

/-- The type class of `A`: `A` itself and everything related to it by a chain of
sort-typed equalities and level variants. -/
def TyCls (A : VExpr) : VExpr → Prop := fun B => A = B ∨ Relation.TransGen (TyStep env U Δ) A B

/-- A definitional equality typed at some member of the set of types `D`. -/
def ElLink (D : VExpr → Prop) (a b : VExpr) : Prop := ∃ X, D X ∧ env.IsDefEq U Δ a b X

/-- One step of an element class: a link or a level variant. -/
def ElStep (D : VExpr → Prop) (a b : VExpr) : Prop :=
  ElLink env U Δ D a b ∨ LvEq U a b ∨ LvEq U b a

/-- The element class of `a` at the set of types `D`. -/
def ElCls (D : VExpr → Prop) (a : VExpr) : VExpr → Prop :=
  fun b => a = b ∨ Relation.TransGen (ElStep env U Δ D) a b

/-- `c` is the element class, at `D`, of a term typed at a member of `D`. -/
def TypedElCls (D c : VExpr → Prop) : Prop :=
  ∃ a X, D X ∧ env.HasType U Δ a X ∧ c = ElCls env U Δ D a

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-! ## Level variants -/

theorem forall₂_equiv_symm : ∀ {ls ls' : List VLevel}, List.Forall₂ (· ≈ ·) ls ls' →
    List.Forall₂ (· ≈ ·) ls' ls
  | _, _, .nil => .nil
  | _, _, .cons h H => .cons h.symm (forall₂_equiv_symm H)

theorem LvEq.symm (h : LvEq U a b) : LvEq U b a := by
  induction h with
  | refl => exact .refl
  | sort h1 h2 h3 => exact .sort h2 h1 h3.symm
  | const h1 h2 h3 => exact .const h2 h1 (forall₂_equiv_symm h3)
  | elim h1 h2 h3 => exact .elim h2 h1 (forall₂_equiv_symm h3)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

theorem LvEq.of_eqUpToLevels (h : EqUpToLevels U a b) : LvEq U a b := by
  induction h with
  | bvar => exact .refl
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

theorem eqUpToLevels_refl {e : VExpr} (h : e.LevelWF U) : EqUpToLevels U e e := by
  have := EqUpToLevels.instL_expr (U := U) e (ls := VLevel.params U) (ls' := VLevel.params U)
    VLevel.params_wf VLevel.params_wf (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl)
  rwa [h.instL_id] at this

/-- A level variant of a term with well-formed levels is an `EqUpToLevels` variant. -/
theorem LvEq.toEqUpToLevels (h : LvEq U a b) (ha : a.LevelWF U) : EqUpToLevels U a b := by
  induction h with
  | refl => exact eqUpToLevels_refl ha
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 ha.1) (ih2 ha.2)
  | lam _ _ ih1 ih2 => exact .lam (ih1 ha.1) (ih2 ha.2)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 ha.1) (ih2 ha.2)
  | proj _ ih => exact .proj (ih ha)

theorem LvEq.subst (h : LvEq U a b) (σ : VExpr.Subst) : LvEq U (a.subst σ) (b.subst σ) := by
  induction h generalizing σ with
  | refl => exact .refl
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 σ) (ih2 σ)
  | lam _ _ ih1 ih2 => exact .lam (ih1 σ) (ih2 σ.lift)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 σ) (ih2 σ.lift)
  | proj _ ih => exact .proj (ih σ)

/-- Level instantiation at pointwise equivalent well-formed levels gives level variants. -/
theorem LvEq.instL (e : VExpr) (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') : LvEq U (e.instL ls) (e.instL ls') :=
  .of_eqUpToLevels (EqUpToLevels.instL_expr e hls hls' heq)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A level variant of a typed term is definitionally equal to it. -/
theorem LvEq.defeq (ha : env.HasType U Δ a X) (h : LvEq U a b) : env.IsDefEq U Δ a b X := by
  have hwf := (ha.levelWF (CtxStrong.strong henv hΔ).levelWF).1
  exact ha.eqUpToLevels henv hΔ (h.toEqUpToLevels hwf)

end

/-! ## Type classes -/

theorem TyStep.symm (h : TyStep env U Δ A B) : TyStep env U Δ B A := by
  rcases h with ⟨u, h⟩ | h | h
  · exact .inl ⟨u, h.symm⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)

theorem TyCls.self : TyCls env U Δ A A := .inl rfl

theorem TyCls.symm (h : TyCls env U Δ A B) : TyCls env U Δ B A := by
  rcases h with rfl | h
  · exact .self
  · refine .inr ?_
    induction h with
    | single h => exact .single h.symm
    | tail _ h ih => exact (Relation.TransGen.single h.symm).trans ih

theorem TyCls.trans (h1 : TyCls env U Δ A B) (h2 : TyCls env U Δ B C) : TyCls env U Δ A C := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact .inr h1
  · exact .inr (h1.trans h2)

/-- Two members of one type class have the same class. -/
theorem TyCls.eq_of_mem (h : TyCls env U Δ A B) : TyCls env U Δ B = TyCls env U Δ A :=
  funext fun _ => propext ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- A single derivable sort-typed equality identifies the type classes. -/
theorem TyCls.eq_of_defeq (h : env.IsDefEq U Δ A B (.sort u)) :
    TyCls env U Δ A = TyCls env U Δ B :=
  (TyCls.eq_of_mem (.inr (.single (.inl ⟨u, h⟩)))).symm

/-- Level variants have the same type class. -/
theorem TyCls.eq_of_lvEq (h : LvEq U A B) : TyCls env U Δ A = TyCls env U Δ B :=
  (TyCls.eq_of_mem (.inr (.single (.inr (.inl h))))).symm

theorem TypeChain.of_lvEq (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hA : env.IsType U Δ A) (h : LvEq U A B) : env.IsDefEq U Δ A B (.sort hA.choose) :=
  LvEq.defeq henv hΔ hA.choose_spec h

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A type class of a type consists of the type and the types chained to it. -/
theorem TyCls.chain_of_isType (hA : env.IsType U Δ A) (h : TyCls env U Δ A B) :
    A = B ∨ env.TypeChain U Δ A B := by
  rcases h with rfl | h
  · exact .inl rfl
  refine .inr ?_
  induction h with
  | single h =>
    rcases h with ⟨u, h⟩ | h | h
    · exact .single h
    · exact .single (TypeChain.of_lvEq henv hΔ hA h)
    · exact .single (TypeChain.of_lvEq henv hΔ hA h.symm)
  | tail _ h ih =>
    have hB := ih.isType_r
    rcases h with ⟨u, h⟩ | h | h
    · exact ih.tail h
    · exact ih.tail (TypeChain.of_lvEq henv hΔ hB h)
    · exact ih.tail (TypeChain.of_lvEq henv hΔ hB h.symm)

/-- For a typed `A`, the type class is exactly the chain-related terms. -/
theorem TyCls.mem_iff_chain (hA : env.HasType U Δ A (.sort u)) :
    TyCls env U Δ A B ↔ env.TypeChain U Δ A B :=
  ⟨fun h => (TyCls.chain_of_isType henv hΔ ⟨_, hA⟩ h).elim (fun e => e ▸ .refl hA) id,
    fun h => .inr (by
      induction h with
      | single h => exact .single (.inl h)
      | tail _ h ih => exact ih.tail (.inl h))⟩

/-- Transport a definitional equality from a member of a type class to its base. -/
theorem TyCls.defeq (hX : TyCls env U Δ X₀ X) (h : env.IsDefEq U Δ e₁ e₂ X) :
    env.IsDefEq U Δ e₁ e₂ X₀ := by
  rcases TyCls.chain_of_isType henv hΔ (h.isType henv hΔ) hX.symm with rfl | hX
  · exact h
  · exact hX.defeqDF h

/-- Transport a definitional equality from the base of a type class to a member. -/
theorem TyCls.defeq_rev (hX : TyCls env U Δ X₀ X) (h : env.IsDefEq U Δ e₁ e₂ X₀) :
    env.IsDefEq U Δ e₁ e₂ X := by
  rcases TyCls.chain_of_isType henv hΔ (h.isType henv hΔ) hX with rfl | hX
  · exact h
  · exact hX.defeqDF h

end

/-! ## Element classes -/

theorem ElLink.symm (h : ElLink env U Δ D a b) : ElLink env U Δ D b a :=
  let ⟨X, hX, h⟩ := h; ⟨X, hX, h.symm⟩

theorem ElStep.symm (h : ElStep env U Δ D a b) : ElStep env U Δ D b a := by
  rcases h with h | h | h
  · exact .inl h.symm
  · exact .inr (.inr h)
  · exact .inr (.inl h)

theorem ElCls.self : ElCls env U Δ D a a := .inl rfl

theorem ElCls.of_link (h : ElLink env U Δ D a b) : ElCls env U Δ D a b := .inr (.single (.inl h))

theorem ElCls.of_lvEq (h : LvEq U a b) : ElCls env U Δ D a b := .inr (.single (.inr (.inl h)))

theorem ElCls.symm (h : ElCls env U Δ D a b) : ElCls env U Δ D b a := by
  rcases h with rfl | h
  · exact .self
  · refine .inr ?_
    induction h with
    | single h => exact .single h.symm
    | tail _ h ih => exact (Relation.TransGen.single h.symm).trans ih

theorem ElCls.trans (h1 : ElCls env U Δ D a b) (h2 : ElCls env U Δ D b c) :
    ElCls env U Δ D a c := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact .inr h1
  · exact .inr (h1.trans h2)

/-- Two members of one element class have the same class. -/
theorem ElCls.eq_of_mem (h : ElCls env U Δ D a b) : ElCls env U Δ D b = ElCls env U Δ D a :=
  funext fun _ => propext ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- A single derivable equality at a member of `D` identifies the element classes. -/
theorem ElCls.eq_of_defeq (hX : D X) (h : env.IsDefEq U Δ a b X) :
    ElCls env U Δ D a = ElCls env U Δ D b :=
  (ElCls.eq_of_mem (.of_link ⟨X, hX, h⟩)).symm

/-- Level variants have the same element class. -/
theorem ElCls.eq_of_lvEq (h : LvEq U a b) : ElCls env U Δ D a = ElCls env U Δ D b :=
  (ElCls.eq_of_mem (.of_lvEq h)).symm

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Collapse lemma**: membership of an element class at a type class `TyCls Δ X₀`, from
a term typed at a member of the class, is one definitional equality at `X₀`. -/
theorem ElCls.collapse (ha : env.HasType U Δ a X) (hX : TyCls env U Δ X₀ X)
    (hb : ElCls env U Δ (TyCls env U Δ X₀) a b) : env.IsDefEq U Δ a b X₀ := by
  have ha0 : env.IsDefEq U Δ a a X₀ := TyCls.defeq henv hΔ hX ha
  rcases hb with rfl | hb
  · exact ha0
  have step : ∀ {y z}, env.IsDefEq U Δ a y X₀ →
      ElStep env U Δ (TyCls env U Δ X₀) y z → env.IsDefEq U Δ a z X₀ := by
    intro y z hy h
    rcases h with ⟨_, hX', h⟩ | h | h
    · exact hy.trans (TyCls.defeq henv hΔ hX' h)
    · exact hy.trans (LvEq.defeq henv hΔ hy.hasType.2 h)
    · exact hy.trans (LvEq.defeq henv hΔ hy.hasType.2 h.symm)
  induction hb with
  | single h => exact step ha0 h
  | tail _ h ih => exact step ih h

/-- Members of a typed element class at `TyCls Δ X₀` are definitionally equal to its
witness at `X₀`, and the class is the class of each of its members. -/
theorem TypedElCls.mem (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    ∃ a, env.IsDefEq U Δ a y X₀ ∧ c = ElCls env U Δ (TyCls env U Δ X₀) a ∧
      c = ElCls env U Δ (TyCls env U Δ X₀) y := by
  obtain ⟨a, X, hX, ha, rfl⟩ := hc
  exact ⟨a, ElCls.collapse henv hΔ ha hX hy, rfl, (ElCls.eq_of_mem hy).symm⟩

/-- Two members of a typed element class at `TyCls Δ X₀` are equal at `X₀`. -/
theorem TypedElCls.defeq (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) (hz : c z) :
    env.IsDefEq U Δ y z X₀ := by
  obtain ⟨a, X, hX, ha, rfl⟩ := hc
  exact (ElCls.collapse henv hΔ ha hX hy).symm.trans (ElCls.collapse henv hΔ ha hX hz)

theorem TypedElCls.hasType (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    env.HasType U Δ y X₀ :=
  let ⟨_, h, _⟩ := hc.mem henv hΔ hy; h.hasType.2

end

theorem TypedElCls.nonempty (hc : TypedElCls env U Δ D c) : ∃ y, c y :=
  let ⟨a, _, _, _, e⟩ := hc; ⟨a, e ▸ .self⟩

theorem TypedElCls.of_hasType (ha : env.HasType U Δ a X₀) :
    TypedElCls env U Δ (TyCls env U Δ X₀) (ElCls env U Δ (TyCls env U Δ X₀) a) :=
  ⟨a, X₀, .self, ha, rfl⟩

/-- Membership of the class of the anchor `a` at `TyCls X₀`. -/
theorem ElCls.mem_of_defeq (h : env.IsDefEq U Δ a b X₀) :
    ElCls env U Δ (TyCls env U Δ X₀) a b := .of_link ⟨X₀, .self, h⟩

theorem TypedElCls.congr_D (hD : D = D') (h : TypedElCls env U Δ D c) :
    TypedElCls env U Δ D' c := hD ▸ h

/-! ## Substitutions with symmetric data -/

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A pair of related substitutions is related in the other order. -/
theorem SubstEq.symm (W : Ctx.SubstEq env U Δ σ σ' Γ) : Ctx.SubstEq env U Δ σ' σ Γ := by
  induction W with
  | nil => exact .nil
  | @cons σ σ' Γ A u W hA hhead ih =>
    refine .cons ih hA ?_
    have hAA := hA.substDF henv W.wf hΔ W
    exact .defeqDF hAA hhead.symm

/-- The right substitution of a related pair is typed. -/
theorem SubstEq.right (W : Ctx.SubstEq env U Δ σ σ' Γ) : Ctx.SubstEq env U Δ σ' σ' Γ :=
  (SubstEq.symm henv hΔ W).left

end

/-! ## Anchored classes -/

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

end

/-! ## Valuations

The model computes every class from the anchor substitution of a valuation, not as a union
over representatives. -/

section
variable (env U Δ)

end

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

end

end Model
end VEnv
end Lean4Lean
