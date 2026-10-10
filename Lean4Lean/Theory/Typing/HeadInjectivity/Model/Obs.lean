import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Classes
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ConstructorMajor

/-! # Observations, subsumption and observation typing

Atomic observations of the glued observation model (section 4.1 of
the design notes): a term denotes the *set* of its observations, so joins are
unions and the typing filter is a property of single observations.

* `Ob`: the observations. `sort ℓ` (the value is a sort of level `ℓ`, the evaluation of the
  level); `piDom D`, `piDomOb o`, `piCod c C`, `piCodOb c K o` (a Pi type with domain type
  class `D`, a domain with observation `o`, a codomain instance at argument class `c` with
  type class `C`, a codomain instance at an argument of class `c` with observations `K`
  having observation `o`); `app D c K o` (a function with domain class `D` which, applied to
  an argument of class `c` with observations covering `K`, has observation `o`);
  `rigid n ℓs m s`, `rigidArg i c` and `rigidArgOb i o` (an application of the rigid constant
  `n` at levels `ℓs` to `m` arguments, of sort `s`, the `i`-th of class `c` or with
  observation `o`); `ctorHead`, `ctorArg`, `ctorArgOb` (the same for constructor applications);
  `fieldOb n j L o` (field `j` of a value of the projection-registered family `n` has
  observation `o`) and the type observations `fieldTy`, `fieldDom` of such a family.
* `Ob.Le o o'` (`o ≼ o'`, "`o'` is weaker"): structural, with key lists compared
  contravariantly: `app D c K o ≼ app D c K' o'` when `K'` covers `K` (`Covers K' K`: every
  key of `K` is subsumed by one of `K'`) and `o ≼ o'`. Reflexive and transitive.
* `TypedOb cv o τs` ("`o`, an observation of a value of class `cv`, is typed at the
  observations `τs` of its type"), an inductive predicate. The value class is read by the
  typing of `app` results (`appCls`) and of field observations (`projCls`).

`TypedOb.strengthen`: typing is stable under replacing the type observations by stronger
ones (this is what transfers typing along `defeqDF`). `TypedOb.not_prop`: nothing is
typed at a list of observations all of which are typed at `[sort 0]` (the observations of a
proposition): the semantic content of proof irrelevance. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Observations. Classes are sets of terms in the target context (`VExpr → Prop`). -/
inductive Ob where
  | sort (ℓ : List Nat → Nat)
  | piDom (D : VExpr → Prop)
  | piDomOb (o : Ob)
  | piCod (c C : VExpr → Prop)
  | piCodOb (c : VExpr → Prop) (K : List Ob) (o : Ob)
  | app (D c : VExpr → Prop) (K : List Ob) (o : Ob)
  /-- A rigid spine of the constant `n` at levels `ℓs` with `nargs` arguments, of sort `s`. -/
  | rigid (n : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat) (s : List Nat → Nat)
  | rigidArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a rigid spine has the observation `o`. -/
  | rigidArgOb (i : Nat) (o : Ob)
  /-- A constructor application of `c` at levels `ℓs` to `nargs` arguments. -/
  | ctorHead (c : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat)
  /-- The `i`-th argument of a constructor application has class `c`. -/
  | ctorArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a constructor application has `o`; `pre` records the keys of
  the earlier arguments (an annotation for typing). -/
  | ctorArgOb (i : Nat) (pre : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)
  /-- Field `j` of a value of the projection-registered family `n` has `o`; `L` lists
  observations of the earlier fields (the typing context, an annotation ignored by `≼`). -/
  | fieldOb (n : Name) (j : Nat) (L : List (List Ob)) (o : Ob)
  /-- A type observation of an application of the projection-registered family `n`: the
  domain of field `j`, at earlier fields with keys `FL`, has the observation `o`. -/
  | fieldTy (n : Name) (j : Nat) (FL : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)
  /-- ... and has type class `D`. -/
  | fieldDom (n : Name) (j : Nat) (FL : List ((VExpr → Prop) × (VExpr → Prop) × List Ob))
      (D : VExpr → Prop)

/-- Subsumption: `Ob.Le o o'` says `o'` is weaker than `o`. Key lists are compared
contravariantly, through an explicit choice function (keeping the definition free of
nested occurrences). -/
inductive Ob.Le : Ob → Ob → Prop
  | refl : Ob.Le o o
  | piDomOb : Ob.Le o o' → Ob.Le (.piDomOb o) (.piDomOb o')
  | piCodOb (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) → Ob.Le o o' →
    Ob.Le (.piCodOb c K o) (.piCodOb c K' o')
  | app (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) → Ob.Le o o' →
    Ob.Le (.app D c K o) (.app D c K' o')
  | rigidArgOb : Ob.Le o o' → Ob.Le (.rigidArgOb i o) (.rigidArgOb i o')
  | ctorArgOb : Ob.Le o o' → Ob.Le (.ctorArgOb i pre o) (.ctorArgOb i pre o')
  | fieldOb : Ob.Le o o' → Ob.Le (.fieldOb n j L o) (.fieldOb n j L' o')
  | fieldTy : Ob.Le o o' → Ob.Le (.fieldTy n j FL o) (.fieldTy n j FL o')

@[inherit_doc] scoped infix:50 " ≼ " => Ob.Le

/-- `Covers K' K`: every observation of `K` is subsumed by one of `K'` (an argument with the
observations `K'` satisfies the demand `K`). -/
def Covers (K' K : List Ob) : Prop := ∀ k ∈ K, ∃ k' ∈ K', k' ≼ k

/-- `Ob.Sub X Y` (`X ⊆ ↑Y`): every observation of `X` is subsumed by one of `Y`. -/
def Ob.Sub (X Y : Ob → Prop) : Prop := ∀ o, X o → ∃ o', Y o' ∧ o' ≼ o

/-! ## Subsumption -/

namespace Ob

theorem _root_.Lean4Lean.VEnv.Model.Covers.choice {K K' : List Ob} (h : Covers K' K) :
    ∃ f : Ob → Ob, (∀ k ∈ K, f k ∈ K') ∧ ∀ k ∈ K, f k ≼ k := by
  classical
  refine ⟨fun k => if hk : k ∈ K then (h k hk).choose else k, ?_, ?_⟩ <;> intro k hk <;>
    simp only [hk, dite_true]
  · exact (h k hk).choose_spec.1
  · exact (h k hk).choose_spec.2

theorem Le.app' (h : Covers K' K) (ho : o ≼ o') : .app D c K o ≼ .app D c K' o' :=
  let ⟨f, h1, h2⟩ := Covers.choice h; .app f h1 h2 ho

theorem Le.piCodOb_of_covers (h : Covers K' K) (ho : o ≼ o') : .piCodOb c K o ≼ .piCodOb c K' o' :=
  let ⟨f, h1, h2⟩ := Covers.choice h; .piCodOb f h1 h2 ho

/-- Pre- and post-composition, proved together by induction on the middle derivation
(key lists are contravariant, so each half needs the other on the keys). -/
theorem Le.trans_aux (h : x ≼ y) : (∀ w, w ≼ x → w ≼ y) ∧ (∀ z, y ≼ z → x ≼ z) := by
  induction h with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | piDomOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piDomOb (ih.1 _ .refl)
      | piDomOb h => exact .piDomOb (ih.1 _ h)
    · cases hz with
      | refl => exact .piDomOb (ih.2 _ .refl)
      | piDomOb h => exact .piDomOb (ih.2 _ h)
  | piCodOb f hf1 hf2 _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piCodOb f hf1 hf2 (iho.1 _ .refl)
      | piCodOb g hg1 hg2 hgo =>
        refine .piCodOb (fun k => f (g k)) (fun k hk => hf1 _ (hg1 k hk))
          (fun k hk => (ihk _ (hg1 k hk)).2 _ (hg2 k hk)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .piCodOb f hf1 hf2 (iho.2 _ .refl)
      | piCodOb g hg1 hg2 hgo =>
        refine .piCodOb (fun k => g (f k)) (fun k hk => hg1 _ (hf1 k hk))
          (fun k hk => (ihk k hk).1 _ (hg2 _ (hf1 k hk))) (iho.2 _ hgo)
  | rigidArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .rigidArgOb (ih.1 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .rigidArgOb (ih.2 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.2 _ h)
  | ctorArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .ctorArgOb (ih.1 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .ctorArgOb (ih.2 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.2 _ h)
  | fieldOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .fieldOb (ih.1 _ .refl)
      | fieldOb h => exact .fieldOb (ih.1 _ h)
    · cases hz with
      | refl => exact .fieldOb (ih.2 _ .refl)
      | fieldOb h => exact .fieldOb (ih.2 _ h)
  | fieldTy _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .fieldTy (ih.1 _ .refl)
      | fieldTy h => exact .fieldTy (ih.1 _ h)
    · cases hz with
      | refl => exact .fieldTy (ih.2 _ .refl)
      | fieldTy h => exact .fieldTy (ih.2 _ h)
  | app f hf1 hf2 _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .app f hf1 hf2 (iho.1 _ .refl)
      | app g hg1 hg2 hgo =>
        refine .app (fun k => f (g k)) (fun k hk => hf1 _ (hg1 k hk))
          (fun k hk => (ihk _ (hg1 k hk)).2 _ (hg2 k hk)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .app f hf1 hf2 (iho.2 _ .refl)
      | app g hg1 hg2 hgo =>
        refine .app (fun k => g (f k)) (fun k hk => hg1 _ (hf1 k hk))
          (fun k hk => (ihk k hk).1 _ (hg2 _ (hf1 k hk))) (iho.2 _ hgo)

theorem Le.trans (h1 : x ≼ y) (h2 : y ≼ z) : x ≼ z := (Le.trans_aux h1).2 _ h2

theorem _root_.Lean4Lean.VEnv.Model.Covers.refl : Covers K K := fun k hk => ⟨k, hk, .refl⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.trans (h1 : Covers K₃ K₂) (h2 : Covers K₂ K₁) : Covers K₃ K₁ := fun k hk =>
  let ⟨k₂, hk₂, l₂⟩ := h2 k hk; let ⟨k₃, hk₃, l₃⟩ := h1 k₂ hk₂; ⟨k₃, hk₃, l₃.trans l₂⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.of_subset (h : ∀ k ∈ K, k ∈ K') : Covers K' K := fun k hk => ⟨k, h k hk, .refl⟩

theorem Sub.refl : Sub X X := fun o h => ⟨o, h, .refl⟩

theorem Sub.trans (h1 : Sub X Y) (h2 : Sub Y Z) : Sub X Z := fun o h =>
  let ⟨o₁, h₁, l₁⟩ := h1 o h; let ⟨o₂, h₂, l₂⟩ := h2 o₁ h₁; ⟨o₂, h₂, l₂.trans l₁⟩

theorem Sub.of_imp (h : ∀ o, X o → Y o) : Sub X Y := fun o ho => ⟨o, h o ho, .refl⟩

/-! ### Inversion -/

theorem Le.sort_inv (h : o ≼ .sort ℓ) : o = .sort ℓ := by cases h; rfl
theorem Le.piDom_inv (h : o ≼ .piDom D) : o = .piDom D := by cases h; rfl
theorem Le.piCod_inv (h : o ≼ .piCod c C) : o = .piCod c C := by cases h; rfl
theorem Le.rigid_inv (h : o ≼ .rigid n ℓs m s) : o = .rigid n ℓs m s := by cases h; rfl
theorem Le.rigidArg_inv (h : o ≼ .rigidArg i c) : o = .rigidArg i c := by cases h; rfl
theorem Le.ctorHead_inv (h : o ≼ .ctorHead c ℓs n) : o = .ctorHead c ℓs n := by cases h; rfl
theorem Le.ctorArg_inv (h : o ≼ .ctorArg i c) : o = .ctorArg i c := by cases h; rfl

theorem Le.ctorArgOb_inv (h : o ≼ .ctorArgOb i pre x) :
    ∃ y, o = .ctorArgOb i pre y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | ctorArgOb h => exact ⟨_, rfl, h⟩

theorem Le.fieldOb_inv (h : o ≼ .fieldOb n j L x) : ∃ L' y, o = .fieldOb n j L' y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl⟩
  | fieldOb h => exact ⟨_, _, rfl, h⟩

theorem Le.fieldTy_inv (h : o ≼ .fieldTy n j FL x) : ∃ y, o = .fieldTy n j FL y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | fieldTy h => exact ⟨_, rfl, h⟩

theorem Le.fieldDom_inv (h : o ≼ .fieldDom n j FL D) : o = .fieldDom n j FL D := by cases h; rfl

theorem Le.piDomOb_inv (h : o ≼ .piDomOb x) : ∃ y, o = .piDomOb y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | piDomOb h => exact ⟨_, rfl, h⟩

theorem Le.piCodOb_inv (h : o ≼ .piCodOb c K x) :
    ∃ K₀ y, o = .piCodOb c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | piCodOb f h1 h2 h3 => exact ⟨_, _, rfl, fun k hk => ⟨f k, h1 k hk, h2 k hk⟩, h3⟩

theorem Le.app_inv (h : o ≼ .app D c K x) :
    ∃ K₀ y, o = .app D c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app f h1 h2 h3 => exact ⟨_, _, rfl, fun k hk => ⟨f k, h1 k hk, h2 k hk⟩, h3⟩

end Ob

/-- Choose, for each element of a list, a related witness: a list of witnesses covering it. -/
theorem exists_list_cover {α β : Type} {P : β → Prop} {R : β → α → Prop} :
    ∀ {L : List α}, (∀ x ∈ L, ∃ y, P y ∧ R y x) →
      ∃ L' : List β, (∀ y ∈ L', P y) ∧ ∀ x ∈ L, ∃ y ∈ L', R y x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨y, hy, hxy⟩ := h x (.head _)
    obtain ⟨L', h1, h2⟩ := exists_list_cover fun x hx => h x (.tail _ hx)
    refine ⟨y :: L', ?_, ?_⟩
    · intro z hz; cases hz with
      | head => exact hy
      | tail _ hz => exact h1 z hz
    · intro z hz; cases hz with
      | head => exact ⟨y, .head _, hxy⟩
      | tail _ hz => let ⟨w, hw, h⟩ := h2 z hz; exact ⟨w, .tail _ hw, h⟩

/-! ## Rigid spine observations -/

/-- A key of a spine observation: domain class, argument class, argument observations. -/
abbrev Key := (VExpr → Prop) × (VExpr → Prop) × List Ob

/-- Wrap an observation in the `app` observations of a spine of keys, outermost first. -/
def wrap (keys : List Key) (o : Ob) : Ob := keys.foldr (fun k o => .app k.1 k.2.1 k.2.2 o) o

@[simp] theorem wrap_nil : wrap [] o = o := rfl
@[simp] theorem wrap_cons : wrap (k :: ks) o = .app k.1 k.2.1 k.2.2 (wrap ks o) := rfl

theorem wrap_append : wrap (ks ++ ks') o = wrap ks (wrap ks' o) := by
  simp [wrap, List.foldr_append]

/-- The innermost observations of a rigid spine after the keys `keys`. -/
def RigidEnd (n : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) (r : Ob) : Prop :=
  (∃ s, r = .rigid n ℓs keys.length s) ∨ ∃ i, ∃ h : i < keys.length, r = .rigidArg i (keys[i]).2.1

/-- An observation that is not an `app` observation. -/
def Ob.NotApp : Ob → Prop
  | .app .. => False
  | _ => True

theorem RigidEnd.notApp (h : RigidEnd n ℓs keys r) : r.NotApp := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

/-- Spines of non-`app` endpoints are determined by the wrapped observation. -/
theorem wrap_inj {ks ks' : List Key} (h : wrap ks o = wrap ks' o') (ho : o.NotApp)
    (ho' : o'.NotApp) : ks = ks' ∧ o = o' := by
  induction ks generalizing ks' with
  | nil =>
    cases ks' with
    | nil => exact ⟨rfl, h⟩
    | cons k ks' => subst h; cases ho
  | cons k ks ih =>
    cases ks' with
    | nil => subst h; cases ho'
    | cons k' ks' =>
      simp only [wrap_cons, Ob.app.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := ih h4
      exact ⟨by rw [← this.1]; obtain ⟨_, _, _⟩ := k; obtain ⟨_, _, _⟩ := k'; simp_all, this.2⟩

/-! ## Backing

A field observation records the observations of the earlier fields (its context `L`); in an
observation set of one value these are *backed*: the set contains the canonical witnesses
`fieldOb n i (L.take i) y` for `y ∈ L[i]`, hereditarily through `app` (same key), `fieldOb`
(same context) and `ctorArgOb`. Typing is inherited by the witnesses (`TypedOb.wit`). -/

/-- The canonical witnesses of an observation. -/
def Ob.wit : Ob → List Ob
  | .fieldOb n j L o =>
    ((List.range L.length).flatMap fun i =>
        ((L[i]?).getD []).map fun y => .fieldOb n i (L.take i) y) ++
      (Ob.wit o).map (.fieldOb n j L ·)
  | .app D c K o => (Ob.wit o).map (.app D c K ·)
  | .ctorArgOb i pre o => (Ob.wit o).map (.ctorArgOb i pre ·)
  | _ => []

/-- An observation set is backed if it contains the canonical witnesses of its members. -/
def Backed (X : Ob → Prop) : Prop := ∀ o, X o → ∀ w ∈ o.wit, X w

theorem Ob.mem_wit_fieldOb {w : Ob} : w ∈ (Ob.fieldOb n j L o).wit ↔
    (∃ i Li y, L[i]? = some Li ∧ y ∈ Li ∧ w = .fieldOb n i (L.take i) y) ∨
    ∃ w', w' ∈ o.wit ∧ w = .fieldOb n j L w' := by
  simp only [Ob.wit, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro (⟨i, hi, y, hy, rfl⟩ | ⟨w', hw', rfl⟩)
    · rw [List.getElem?_eq_getElem hi] at hy
      exact .inl ⟨i, _, y, List.getElem?_eq_getElem hi, hy, rfl⟩
    · exact .inr ⟨w', hw', rfl⟩
  · rintro (⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w', hw', rfl⟩)
    · refine .inl ⟨i, (List.getElem?_eq_some_iff.1 hLi).1, y, ?_, rfl⟩
      rw [hLi]; exact hy
    · exact .inr ⟨w', hw', rfl⟩

/-! ### Finite closure under witnesses -/

mutual
/-- A size of observations along which witnesses decrease. -/
def Ob.sz : Ob → Nat
  | .fieldOb _ _ L o => 1 + Ob.szLL L + Ob.sz o
  | .app _ _ _ o => 1 + Ob.sz o
  | .ctorArgOb _ _ o => 1 + Ob.sz o
  | _ => 1
def Ob.szL : List Ob → Nat
  | [] => 0
  | o :: l => Ob.sz o + Ob.szL l
def Ob.szLL : List (List Ob) → Nat
  | [] => 0
  | K :: L => 1 + Ob.szL K + Ob.szLL L
end

theorem Ob.sz_le_szL : ∀ {K : List Ob} {y : Ob}, y ∈ K → y.sz ≤ Ob.szL K
  | _ :: _, _, .head _ => by simp only [Ob.szL]; omega
  | _ :: _, _, .tail _ h => by have := Ob.sz_le_szL h; simp only [Ob.szL]; omega

theorem Ob.szLL_take : ∀ {L : List (List Ob)} {i : Nat} {Li : List Ob} {y : Ob},
    L[i]? = some Li → y ∈ Li → Ob.szLL (L.take i) + y.sz < Ob.szLL L
  | K :: L, 0, Li, y, h, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    have := Ob.sz_le_szL hy
    simp only [List.take_zero, Ob.szLL]; omega
  | K :: L, i+1, Li, y, h, hy => by
    simp only [List.getElem?_cons_succ] at h
    have := Ob.szLL_take h hy
    simp only [List.take_succ_cons, Ob.szLL]; omega

theorem Ob.sz_wit : ∀ {o w : Ob}, w ∈ o.wit → w.sz < o.sz
  | .fieldOb n j L o, w, h => by
    rcases Ob.mem_wit_fieldOb.1 h with ⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w', hw', rfl⟩
    · have := Ob.szLL_take hLi hy; simp only [Ob.sz]; omega
    · have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .app D c K o, w, h => by
    simp only [Ob.wit, List.mem_map] at h
    obtain ⟨w', hw', rfl⟩ := h
    have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .ctorArgOb i pre o, w, h => by
    simp only [Ob.wit, List.mem_map] at h
    obtain ⟨w', hw', rfl⟩ := h
    have := Ob.sz_wit hw'; simp only [Ob.sz]; omega
  | .sort _, _, h | .piDom _, _, h | .piDomOb _, _, h | .piCod _ _, _, h | .piCodOb _ _ _, _, h
  | .rigid _ _ _ _, _, h | .rigidArg _ _, _, h | .rigidArgOb _ _, _, h | .ctorHead _ _ _, _, h
  | .ctorArg _ _, _, h | .fieldTy _ _ _ _, _, h | .fieldDom _ _ _ _, _, h => by
    simp [Ob.wit] at h

/-- An observation with all its witnesses, hereditarily. -/
def Ob.cl (o : Ob) : List Ob := o :: o.wit.attach.flatMap fun ⟨w, _⟩ => Ob.cl w
termination_by o.sz
decreasing_by exact Ob.sz_wit ‹_›

theorem Ob.mem_cl_self (o : Ob) : o ∈ o.cl := by unfold Ob.cl; exact List.mem_cons_self ..

theorem Ob.cl_sub (hX : Backed X) : ∀ {o : Ob}, X o → ∀ w ∈ o.cl, X w
  | o, ho, w, hw => by
    unfold Ob.cl at hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ho
    · simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hw
      obtain ⟨w', hw', hw⟩ := hw
      have := Ob.sz_wit hw'
      exact Ob.cl_sub hX (hX o ho w' hw') w hw
termination_by o => o.sz

theorem Ob.cl_closed : ∀ {o v w : Ob}, v ∈ o.cl → w ∈ v.wit → w ∈ o.cl
  | o, v, w, hv, hw => by
    unfold Ob.cl at hv ⊢
    rcases List.mem_cons.1 hv with rfl | hv
    · refine List.mem_cons_of_mem _ ?_
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
      exact ⟨w, hw, Ob.mem_cl_self w⟩
    · simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hv
      obtain ⟨w', hw', hv⟩ := hv
      have := Ob.sz_wit hw'
      refine List.mem_cons_of_mem _ ?_
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
      exact ⟨w', hw', Ob.cl_closed hv hw⟩
termination_by o => o.sz

/-- **Closure**: a finite part of a backed set extends to a finite backed part. -/
theorem Backed.close {X : Ob → Prop} {K : List Ob} (hX : Backed X) (hK : ∀ k ∈ K, X k) :
    ∃ K' : List Ob, (∀ k ∈ K, k ∈ K') ∧ (∀ k ∈ K', X k) ∧ Backed (· ∈ K') := by
  refine ⟨K.flatMap Ob.cl, fun k hk => List.mem_flatMap.2 ⟨k, hk, Ob.mem_cl_self k⟩,
    fun k hk => ?_, fun v hv w hw => ?_⟩
  · obtain ⟨o, ho, hk⟩ := List.mem_flatMap.1 hk
    exact Ob.cl_sub hX (hK o ho) k hk
  · obtain ⟨o, ho, hv⟩ := List.mem_flatMap.1 hv
    exact List.mem_flatMap.2 ⟨o, ho, Ob.cl_closed hv hw⟩

/-! ## Observation typing -/

/-- A level evaluated at evaluated level parameters. -/
def _root_.Lean4Lean.VLevel.evalAt (w : VLevel) (ℓs : List (List Nat → Nat)) : List Nat → Nat :=
  fun ns => w.eval (ℓs.map (· ns))

theorem _root_.Lean4Lean.VLevel.eval_inst_eq_evalAt (w : VLevel) (ls : List VLevel) :
    (w.inst ls).eval = w.evalAt (ls.map (·.eval)) := by
  funext ns; simp [VLevel.evalAt, VLevel.eval_inst, List.map_map, Function.comp_def]

section
variable (env : VEnv)

/-- The type of the constant `c` returns an application of the constant `I`. -/
def CtorFam (c I : Name) : Prop :=
  ∃ ci ls, env.constants c = some ci ∧ ci.type.forallResult.getAppFnArgs.1 = .const I ls

/-- The family indicator for the constructor `c` in the type observations `τs`: a rigid
observation of `c`'s family whose sort is not zero. -/
def CtorTyped (c : Name) (τs : List Ob) : Prop :=
  ∃ I ℓs m s, .rigid I ℓs m s ∈ τs ∧ CtorFam env c I ∧ s ≠ (fun _ => 0) ∧
    ∀ info, ¬ env.projections I info

end

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The applications of members of `cv` to members of `c`, closed in the element class at
`C`: the value class of the result of applying a value of class `cv` to an argument of class
`c`, when the codomain at that argument has type class `C`. -/
def appCls (cv c C : VExpr → Prop) : VExpr → Prop :=
  fun z => ∃ w y, cv w ∧ c y ∧ ElCls env U Δ C (.app w y) z

/-- The projections of members of `cv` onto field `j` of `n`, closed in the element class at
`D`: the value class of field `j` of a value of class `cv`. -/
def projCls (n : Name) (j : Nat) (cv D : VExpr → Prop) : VExpr → Prop :=
  fun z => ∃ w, cv w ∧ ElCls env U Δ D (.proj n j w) z

/-- The keys `FL` of the earlier fields in a type observation of a field are compatible with
the context `L` of a field observation of a value of class `cv`: each key class is a class of
projections of `cv`, and each key observation is weaker than a context observation. -/
def FLCompat (n : Name) (cv : VExpr → Prop) (L : List (List Ob)) (FL : List Key) : Prop :=
  FL.length = L.length ∧ ∀ i F Li, FL[i]? = some F → L[i]? = some Li →
    (∃ Di, F.2.1 = projCls env U Δ n i cv Di) ∧ ∀ y ∈ F.2.2, ∃ y' ∈ Li, y' ≼ y

/-- `TypedOb cv o τs`: the observation `o` of a value of class `cv` is typed at the observations
`τs` of its type. Sorts are typed at their successor; type observations at some sort, a
codomain observation at a level that vanishes whenever the Pi's level does (so that
observations of propositions are typed at `sort 0` only); an `app` observation needs the Pi's
domain class, its keys typed (at their own class) at observations of the domain, its argument
class typed, and its result typed, at the class of the applications (`appCls`, the codomain
class read from `piCod`), at observations of the codomain instance at a key list it covers.
The value class is also used by field observations. -/
inductive TypedOb : (VExpr → Prop) → Ob → List Ob → Prop
  | sort : .sort (fun ns => ℓ ns + 1) ∈ τs → TypedOb cv (.sort ℓ) τs
  | piDom : .sort ℓ ∈ τs → TypedOb cv (.piDom D) τs
  | piDomOb : .sort ℓ ∈ τs → TypedOb cv (.piDomOb o) τs
  | piCod : .sort ℓ ∈ τs → TypedOb cv (.piCod c C) τs
  | piCodOb : .sort ℓ ∈ τs → TypedOb cv' o [.sort ℓ'] → (∀ ns, ℓ ns = 0 → ℓ' ns = 0) →
    TypedOb cv (.piCodOb c K o) τs
  | app : .piDom D ∈ τs → (∀ x ∈ τd, .piDomOb x ∈ τs) → (∀ k ∈ K, TypedOb c k τd) →
    Backed (· ∈ K) → TypedElCls env U Δ D c → .piCod c C ∈ τs →
    (∀ x ∈ τc, ∃ K₀, .piCodOb c K₀ x ∈ τs ∧ Covers K K₀) →
    TypedOb (appCls env U Δ cv c C) o τc → TypedOb cv (.app D c K o) τs
  | rigid : .sort s ∈ τs → TypedOb cv (.rigid n ℓs m s) τs
  | rigidArg : .sort ℓ ∈ τs → TypedOb cv (.rigidArg i c) τs
  | rigidArgOb : .sort ℓ ∈ τs → TypedOb cv (.rigidArgOb i o) τs
  | ctorHead : CtorTyped env c τs → TypedOb cv (.ctorHead c ℓs m) τs
  | ctorArg : CtorTyped env c τs → TypedOb cv (.ctorArg i cls) τs
  | ctorArgOb : CtorTyped env c τs → TypedOb cv (.ctorArgOb i pre o) τs
  | fieldTy : .sort ℓ ∈ τs → (∀ ns, ℓ ns ≠ 0) → TypedOb cv (.fieldTy n j FL o) τs
  | fieldDom : .sort ℓ ∈ τs → (∀ ns, ℓ ns ≠ 0) → TypedOb cv (.fieldDom n j FL D) τs
  /-- A field observation of a value of class `cv`: the value's type is an application of the
  projection-registered family `n` with a field-domain observation of field `j` (of class `D`
  at keys `FL` for the earlier fields compatible with the context `L`); the observation `o` is
  typed, at the class of the projections, at field-type observations of the type at keys
  compatible with `L`; and the context observations are typed field observations themselves. -/
  | fieldOb : env.projections n info → j < info.numFields → L.length = j →
    .fieldDom n j FL D ∈ τs → FLCompat env U Δ n cv L FL →
    (∀ x ∈ τd, ∃ FLx, .fieldTy n j FLx x ∈ τs ∧ FLCompat env U Δ n cv L FLx) →
    TypedOb (projCls env U Δ n j cv D) o τd →
    (∀ i Li, L[i]? = some Li → ∀ y ∈ Li, TypedOb cv (.fieldOb n i (L.take i) y) τs) →
    TypedOb cv (.fieldOb n j L o) τs

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- Typing is stable under replacing the type observations by stronger ones. -/
theorem TypedOb.strengthen (H : TypedOb env U Δ cv o τs) (h : Covers τs' τs) :
    TypedOb env U Δ cv o τs' := by
  induction H generalizing τs' with
  | sort h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .sort h2
  | piDom h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDom h2
  | piDomOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDomOb h2
  | piCod h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCod h2
  | piCodOb h1 h3 h4 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCodOb h2 h3 h4
  | rigid h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigid h2
  | ctorHead h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4, h5⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorHead ⟨I, ℓs, m, s, h2, h3, h4, h5⟩
  | ctorArg h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4, h5⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorArg ⟨I, ℓs, m, s, h2, h3, h4, h5⟩
  | ctorArgOb h1 =>
    obtain ⟨I, ℓs, m, s, h1, h3, h4, h5⟩ := h1
    obtain ⟨_, h2, l⟩ := h _ h1; cases l.rigid_inv; exact .ctorArgOb ⟨I, ℓs, m, s, h2, h3, h4, h5⟩
  | rigidArg h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArg h2
  | rigidArgOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArgOb h2
  | fieldTy h1 hz => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .fieldTy h2 hz
  | fieldDom h1 hz => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .fieldDom h2 hz
  | @fieldOb n info j τs cv L FL τd D o hp hj hL hD hFL hτd _ _ iho ihrec =>
    obtain ⟨_, hD', lD⟩ := h _ hD; cases lD.fieldDom_inv
    have ⟨τd', hd1, hd2⟩ := exists_list_cover (L := τd)
      (P := fun y => ∃ FLx, Ob.fieldTy n j FLx y ∈ τs' ∧ FLCompat env U Δ n cv L FLx)
      (R := fun y x => y ≼ x) fun x hx => by
        obtain ⟨FLx, h3, h4⟩ := hτd x hx
        have ⟨_, h5, l⟩ := h _ h3
        have ⟨y, e, l'⟩ := l.fieldTy_inv; subst e; exact ⟨y, ⟨FLx, h5, h4⟩, l'⟩
    exact .fieldOb hp hj hL hD' hFL hd1 (iho hd2) (fun i Li hi y hy => ihrec i Li hi y hy h)
  | @app _ τd K c _ τc _ C _ hD hd _ hB hc hC hcod _ ihk iho =>
    have ⟨_, h2, l⟩ := h _ hD; cases l.piDom_inv
    have ⟨_, hC', lC⟩ := h _ hC; cases lC.piCod_inv
    have ⟨τd', hd1, hd2⟩ := exists_list_cover (L := τd) (P := fun y => Ob.piDomOb y ∈ τs')
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨_, h3, l⟩ := h _ (hd x hx)
        have ⟨y, e, l'⟩ := l.piDomOb_inv; subst e; exact ⟨y, h3, l'⟩
    have ⟨τc', hc1, hc2⟩ := exists_list_cover (L := τc)
      (P := fun y => ∃ K₀, Ob.piCodOb c K₀ y ∈ τs' ∧ Covers K K₀)
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨K₀, h3, hK⟩ := hcod x hx
        have ⟨_, h4, l⟩ := h _ h3
        have ⟨K₁, y, e, hK₁, l'⟩ := l.piCodOb_inv; subst e
        exact ⟨y, ⟨K₁, h4, hK.trans hK₁⟩, l'⟩
    exact .app h2 hd1 (fun k hk => ihk k hk hd2) hB hc hC' hc1 (iho hc2)

theorem TypedOb.mono (H : TypedOb env U Δ cv o τs) (h : ∀ τ ∈ τs, τ ∈ τs') :
    TypedOb env U Δ cv o τs' := H.strengthen (.of_subset h)

/-- The observation of the zero level. -/
abbrev zeroF : List Nat → Nat := fun _ => 0

theorem TypedOb.not_sort_zero (H : TypedOb env U Δ cv (.sort ℓ) [.sort zeroF]) : False := by
  cases H with
  | sort h =>
    simp only [List.mem_singleton, Ob.sort.injEq] at h
    exact Nat.succ_ne_zero _ (congrFun h [])

theorem TypedOb.sort_congr (H : TypedOb env U Δ cv o [.sort ℓ]) (e : ∀ ns, ℓ ns = ℓ' ns) :
    TypedOb env U Δ cv o [.sort ℓ'] := by
  have : ℓ = ℓ' := funext e
  subst this; exact H

/-- **Proof irrelevance, semantically**: nothing is typed at a list of observations each of
which is typed at `[sort 0]`. -/
theorem TypedOb.not_prop (H : TypedOb env U Δ cv o τs)
    (h : ∀ τ ∈ τs, ∃ cv', TypedOb env U Δ cv' τ [.sort zeroF]) : False := by
  induction H with
  | sort h1 | piDom h1 | piDomOb h1 | piCod h1 | piCodOb h1 | rigid h1 | rigidArg h1
  | rigidArgOb h1 =>
    obtain ⟨_, h⟩ := h _ h1; exact h.not_sort_zero
  | fieldTy h1 hz | fieldDom h1 hz =>
    obtain ⟨_, h⟩ := h _ h1
    cases h with
    | sort h2 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h2
      exact Nat.succ_ne_zero _ (congrFun h2 [])
  | ctorHead h1 | ctorArg h1 | ctorArgOb h1 =>
    obtain ⟨I, ℓs, m, s, h1, -, hne, -⟩ := h1
    obtain ⟨_, h⟩ := h _ h1
    cases h with
    | rigid h2 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h2
      exact hne h2
  | fieldOb _ _ _ hD =>
    obtain ⟨_, h⟩ := h _ hD
    cases h with
    | fieldDom h2 hz =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h2
      subst h2; exact hz [] rfl
  | app _ _ _ _ _ _ hcod _ _ iho =>
    refine iho fun x hx => ?_
    have ⟨_, h3, _⟩ := hcod x hx
    obtain ⟨_, h⟩ := h _ h3
    cases h with
    | piCodOb h4 h5 h6 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h4; subst h4
      exact ⟨_, h5.sort_congr fun ns => h6 ns rfl⟩

/-- **Typing is inherited by the canonical witnesses.** -/
theorem TypedOb.wit (H : TypedOb env U Δ cv o τs) : ∀ w ∈ o.wit, TypedOb env U Δ cv w τs := by
  induction H with
  | app hD hd hk hB hc hC hcod _ _ iho =>
    intro w hw
    simp only [Ob.wit, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact .app hD hd hk hB hc hC hcod (iho w' hw')
  | ctorArgOb h => intro w hw; simp only [Ob.wit, List.mem_map] at hw
                   obtain ⟨w', -, rfl⟩ := hw; exact .ctorArgOb h
  | fieldOb hp hj hL hD hFL hτd ho hrec iho _ =>
    intro w hw
    rcases Ob.mem_wit_fieldOb.1 hw with ⟨i, Li, y, hLi, hy, rfl⟩ | ⟨w', hw', rfl⟩
    · exact hrec i Li hLi y hy
    · exact .fieldOb hp hj hL hD hFL hτd (iho w' hw') hrec
  | _ => intro w hw; simp [Ob.wit] at hw

end Model
end VEnv
end Lean4Lean
