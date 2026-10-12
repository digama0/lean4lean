import Lean4Lean.ExprUniverses
import Lean4Lean.Verify.Expr

/-!
# Closure lemmas for the universe-scope check

`Expr.levelParamsIn params e` (`Lean4Lean/ExprUniverses.lean`) checks that every universe
parameter of `e` is in `params`. This file proves that the check is preserved by abstraction,
instantiation, level instantiation, application spines, literal expansion and `==`, and that a
level substitution fixing `params` is the identity on an expression that passes it. The
universe-support invariant of the verified type checker (`VContext.LevelsBelow`) is built on it.
-/

namespace Lean

@[simp] theorem Expr.levelParamsIn_abstract1 (e : Expr) (fv : FVarId) (k : Nat) :
    (e.abstract1 fv k).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [abstract1, levelParamsIn, *]
  all_goals split <;> rfl

@[simp] theorem Expr.levelParamsIn_abstractList (e : Expr) (fvs : List FVarId) (k : Nat) :
    (e.abstractList fvs k).levelParamsIn params = e.levelParamsIn params := by
  induction fvs generalizing e <;> simp [abstractList, *]

@[simp] theorem Expr.levelParamsIn_abstractN (e : Expr) (fvs : List FVarId) (k : Nat) :
    (e.abstractN fvs k).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [abstractN, levelParamsIn, *]
  all_goals split <;> rfl

theorem Level.paramsIn_subst_fixed {u : Level}
    (H : u.paramsIn params = true)
    (hfix : ∀ name ∈ params, F name = .param name) :
    u.substParams' F false = u := by
  induction u <;> simp_all [paramsIn, substParams']

/-- A successful concrete universe-scope check makes nonreducing
substitution of every other universe parameter the identity. -/
theorem Expr.levelParamsIn_subst_fixed {e : Expr}
    (H : e.levelParamsIn params = true)
    (hfix : ∀ name ∈ params, F name = .param name) :
    e.instantiateLevelParamsCore' false F = e := by
  induction e <;> simp_all [levelParamsIn, instantiateLevelParamsCore']
  case sort u => exact Level.paramsIn_subst_fixed H hfix
  case const name levels =>
    conv => rhs; rw [← List.map_id (l := levels)]
    apply List.map_congr_left
    intro u hu
    exact Level.paramsIn_subst_fixed (H u hu) hfix

@[simp] theorem Expr.levelParamsIn_liftLooseBVars (e : Expr) (k n : Nat) :
    (e.liftLooseBVars' k n).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [liftLooseBVars', levelParamsIn, *]

theorem Expr.levelParamsIn_instantiate1 {e arg : Expr}
    (he : e.levelParamsIn params = true) (ha : arg.levelParamsIn params = true) :
    (e.instantiate1' arg k).levelParamsIn params = true := by
  induction e generalizing k <;> simp_all [instantiate1', levelParamsIn]
  split <;> simp_all [levelParamsIn]
  split <;> simp_all [levelParamsIn]

theorem Expr.levelParamsIn_instantiateList {e : Expr} {args : List Expr}
    (he : e.levelParamsIn params = true) (ha : ∀ arg ∈ args, arg.levelParamsIn params = true) :
    (e.instantiateList args k).levelParamsIn params = true := by
  induction args generalizing e with
  | nil => exact he
  | cons a args ih =>
    exact ih (Expr.levelParamsIn_instantiate1 he (ha a (by simp))) (fun a h => ha a (by simp [h]))

open private mkLevelMaxCore mkLevelIMaxCore from Lean.Level in
theorem Level.paramsIn_mkMax (hu : u.paramsIn params = true) (hv : v.paramsIn params = true) :
    (mkLevelMax' u v).paramsIn params = true := by
  unfold mkLevelMax' mkLevelMaxCore
  dsimp only
  repeat' first
  | exact hu
  | exact hv
  | exact show (u.paramsIn params && v.paramsIn params) = true by rw [hu, hv]; rfl
  | split
  all_goals simp_all only [mkLevelMax, Level.paramsIn, Bool.and_eq_true, and_self]

open private mkLevelIMaxCore from Lean.Level in
theorem Level.paramsIn_mkIMax (hu : u.paramsIn params = true) (hv : v.paramsIn params = true) :
    (mkLevelIMax' u v).paramsIn params = true := by
  unfold mkLevelIMax' mkLevelIMaxCore
  repeat' first
  | exact Level.paramsIn_mkMax hu hv
  | exact hu
  | exact hv
  | exact show (u.paramsIn params && v.paramsIn params) = true by rw [hu, hv]; rfl
  | split

theorem Level.paramsIn_subst {u : Level}
    (hu : u.paramsIn sourceParams = true)
    (hf : ∀ name ∈ sourceParams, (f name).paramsIn params = true) :
    (u.substParams' f red).paramsIn params = true := by
  induction u generalizing red with
  | zero => rfl
  | mvar => cases hu
  | param => exact hf _ (by simpa [Level.paramsIn] using hu)
  | succ u ih => exact ih hu
  | max u v ihu ihv =>
    have h : u.paramsIn sourceParams = true ∧ v.paramsIn sourceParams = true := by
      simpa only [Level.paramsIn, Bool.and_eq_true] using hu
    simp only [Level.substParams']
    split
    · exact Level.paramsIn_mkMax (ihu h.1) (ihv h.2)
    · simpa only [Level.paramsIn, Bool.and_eq_true] using And.intro (ihu h.1) (ihv h.2)
  | imax u v ihu ihv =>
    have h : u.paramsIn sourceParams = true ∧ v.paramsIn sourceParams = true := by
      simpa only [Level.paramsIn, Bool.and_eq_true] using hu
    simp only [Level.substParams']
    split
    · exact Level.paramsIn_mkIMax (ihu h.1) (ihv h.2)
    · simpa only [Level.paramsIn, Bool.and_eq_true] using And.intro (ihu h.1) (ihv h.2)

theorem Expr.levelParamsIn_instantiateLevelParamsCore {e : Expr}
    (he : e.levelParamsIn sourceParams = true)
    (hf : ∀ name ∈ sourceParams, (f name).paramsIn params = true) :
    (e.instantiateLevelParamsCore' red f).levelParamsIn params = true := by
  induction e <;> simp_all [Expr.levelParamsIn, Expr.instantiateLevelParamsCore']
  case sort => exact Level.paramsIn_subst he hf
  case const => exact fun l hl => Level.paramsIn_subst (he l hl) hf

theorem Expr.levelParamsIn_instantiateLevelParams {e : Expr}
    (he : e.levelParamsIn sourceParams = true)
    (hlevels : ∀ l ∈ levels, l.paramsIn params = true)
    (hlen : sourceParams.length = levels.length) :
    (e.instantiateLevelParams sourceParams levels).levelParamsIn params = true := by
  rw [Expr.instantiateLevelParams_eq]
  apply Expr.levelParamsIn_instantiateLevelParamsCore he
  intro name hm
  cases hidx : sourceParams.idxOf? name with
  | none => exact False.elim ((List.idxOf?_eq_none_iff.mp hidx) hm)
  | some i =>
    obtain ⟨hi, _, _⟩ := List.idxOf?_eq_some_iff.mp hidx
    have hi' : i < levels.length := by omega
    simp only [Option.bind_some, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hlevels _ (List.getElem_mem hi')

theorem Expr.levelParamsIn_getAppFn {e : Expr} (he : e.levelParamsIn params = true) :
    e.getAppFn.levelParamsIn params = true := by
  induction e <;> simp_all [Expr.getAppFn, Expr.levelParamsIn]

theorem Expr.levelParamsIn_getAppArgsRevList {e : Expr} (he : e.levelParamsIn params = true) :
    ∀ arg ∈ e.getAppArgsRevList, arg.levelParamsIn params = true := by
  induction e <;> simp_all [Expr.getAppArgsRevList, Expr.levelParamsIn]

theorem Expr.levelParamsIn_mkAppRevList {e : Expr} {args : List Expr}
    (he : e.levelParamsIn params = true) (ha : ∀ arg ∈ args, arg.levelParamsIn params = true) :
    (e.mkAppRevList args).levelParamsIn params = true := by
  induction args with
  | nil => exact he
  | cons a args ih =>
    simp only [Expr.mkAppRevList, Expr.levelParamsIn, Bool.and_eq_true]
    exact ⟨ih (fun a h => ha a (by simp [h])), ha a (by simp)⟩

theorem Expr.levelParamsIn_mkAppRevList_iff {e : Expr} {args : List Expr} :
    (e.mkAppRevList args).levelParamsIn params = true ↔
      e.levelParamsIn params = true ∧ ∀ a ∈ args, a.levelParamsIn params = true := by
  induction args <;> simp_all [Expr.mkAppRevList, Expr.levelParamsIn, and_comm, and_left_comm]

theorem Expr.levelParamsIn_mkAppList_iff {e : Expr} {args : List Expr} :
    (e.mkAppList args).levelParamsIn params = true ↔
      e.levelParamsIn params = true ∧ ∀ a ∈ args, a.levelParamsIn params = true := by
  simp [← Expr.mkAppRevList_reverse, Expr.levelParamsIn_mkAppRevList_iff]

theorem Expr.levelParamsIn_mkAppList {e : Expr} {args : List Expr}
    (he : e.levelParamsIn params = true) (ha : ∀ a ∈ args, a.levelParamsIn params = true) :
    (e.mkAppList args).levelParamsIn params = true :=
  Expr.levelParamsIn_mkAppList_iff.2 ⟨he, ha⟩

theorem Expr.levelParamsIn_of_mem_getAppArgsList {e a : Expr}
    (he : e.levelParamsIn params = true) (ha : a ∈ e.getAppArgsList) :
    a.levelParamsIn params = true := by
  rw [← e.mkAppList_getAppArgsList, Expr.levelParamsIn_mkAppList_iff] at he
  exact he.2 a ha

theorem Expr.levelParamsIn_of_mem_getAppArgs {e a : Expr}
    (he : e.levelParamsIn params = true) (ha : a ∈ e.getAppArgs) :
    a.levelParamsIn params = true :=
  Expr.levelParamsIn_of_mem_getAppArgsList he (by
    rw [← Expr.getAppArgs_toList]; exact Array.mem_toList_iff.2 ha)

theorem Expr.levelParamsIn_getElem!_of_forall {args : Array Expr}
    (ha : ∀ a ∈ args, a.levelParamsIn params = true) (i : Nat) :
    (args[i]!).levelParamsIn params = true := by
  by_cases h : i < args.size
  · rw [getElem!_pos args i h]; exact ha _ (Array.getElem_mem h)
  · rw [getElem!_neg args i h]; rfl

open private mkAppRangeAux from Lean.Expr in
theorem Expr.levelParamsIn_mkAppRange {f : Expr} {args : Array Expr}
    (hf : f.levelParamsIn params = true) (ha : ∀ a ∈ args, a.levelParamsIn params = true) :
    (mkAppRange f i j args).levelParamsIn params = true := by
  unfold mkAppRange
  suffices ∀ k i f, j - i = k → f.levelParamsIn params = true →
      (mkAppRangeAux j args i f).levelParamsIn params = true from this _ _ _ rfl hf
  intro k; induction k with
  | zero => intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [omega; exact hf]
  | succ k ih =>
    intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [skip; exact hf]
    refine ih _ _ (by omega) ?_
    simp [Expr.levelParamsIn, hf, Expr.levelParamsIn_getElem!_of_forall ha]

theorem Expr.levelParamsIn_natLitToConstructor :
    (Expr.natLitToConstructor n).levelParamsIn params = true := by
  cases n <;> simp [Expr.natLitToConstructor, Expr.natZero, Expr.natSucc, Expr.levelParamsIn]

theorem Expr.levelParamsIn_strLitToConstructor :
    (Expr.strLitToConstructor s).levelParamsIn params = true := by
  simp [Expr.strLitToConstructor, Expr.levelParamsIn]
  induction s.toList <;> simp [*, Expr.levelParamsIn, Level.paramsIn]

@[simp] theorem Expr.levelParamsIn_lowerLooseBVars (e : Expr) (k n : Nat) :
    (e.lowerLooseBVars' k n).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp only [lowerLooseBVars'] <;> (try split) <;>
    simp [levelParamsIn, *]

theorem Level.paramsIn_foldl_mkIMax {us : List Level}
    (hus : ∀ u ∈ us, u.paramsIn params = true) (hs : s.paramsIn params = true) :
    (us.foldl (fun x y => mkLevelIMax' y x) s).paramsIn params = true := by
  induction us generalizing s with
  | nil => exact hs
  | cons u us ih =>
    exact ih (fun v h => hus v (.tail _ h)) (Level.paramsIn_mkIMax (hus u (.head _)) hs)

theorem Expr.levelParamsIn_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) :
    e₁.levelParamsIn params = e₂.levelParamsIn params := by
  simp [(· == ·)] at h
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ at h; cases h)
  all_goals simp [Expr.eqv'] at h; simp [Expr.levelParamsIn] <;> grind
end Lean
