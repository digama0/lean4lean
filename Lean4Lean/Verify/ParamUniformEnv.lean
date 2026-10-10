import Lean4Lean.Verify.ExprParamUniform
import Lean4Lean.Declaration

/-!
# Parameter uniformity through the type checker: syntactic layer

The parameter-uniformity invariant of the verified type checker (`VContext.ParamUniformBelow` in
`Lean4Lean/Verify/TypeChecker/Basic.lean`) tracks, besides `Expr.ParamUniform`, that every projection
node names a structure whose constructors are compatible with the head set (`Expr.ProjsOK`), and
it constrains the environment by `EnvParamUniform`. This file collects the definitions and the purely
syntactic closure lemmas they need: substitution, abstraction, application spines, level
instantiation, beta reduction, and the parameter telescopes of head constants.
-/

namespace Lean.Expr

open Lean4Lean

/-! ### Projection names -/

/-- Every projection node `.proj s _ _` of `e` satisfies `ok s`. -/
def ProjsOK (ok : Name → Prop) : Expr → Prop
  | .app f a => ProjsOK ok f ∧ ProjsOK ok a
  | .lam _ t b _ => ProjsOK ok t ∧ ProjsOK ok b
  | .forallE _ t b _ => ProjsOK ok t ∧ ProjsOK ok b
  | .letE _ t v b _ => ProjsOK ok t ∧ ProjsOK ok v ∧ ProjsOK ok b
  | .mdata _ e => ProjsOK ok e
  | .proj s _ e => ok s ∧ ProjsOK ok e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => True

namespace ProjsOK

variable {ok : Name → Prop}

@[simp] theorem app_iff : ProjsOK ok (.app f a) ↔ ProjsOK ok f ∧ ProjsOK ok a := .rfl
@[simp] theorem lam_iff : ProjsOK ok (.lam n t b bi) ↔ ProjsOK ok t ∧ ProjsOK ok b := .rfl
@[simp] theorem forallE_iff : ProjsOK ok (.forallE n t b bi) ↔ ProjsOK ok t ∧ ProjsOK ok b := .rfl
@[simp] theorem letE_iff :
    ProjsOK ok (.letE n t v b nd) ↔ ProjsOK ok t ∧ ProjsOK ok v ∧ ProjsOK ok b := .rfl
@[simp] theorem mdata_iff : ProjsOK ok (.mdata m e) ↔ ProjsOK ok e := .rfl
@[simp] theorem proj_iff : ProjsOK ok (.proj s i e) ↔ ok s ∧ ProjsOK ok e := .rfl
@[simp] theorem bvar : ProjsOK ok (.bvar i) := trivial
@[simp] theorem fvar : ProjsOK ok (.fvar fv) := trivial
@[simp] theorem mvar : ProjsOK ok (.mvar mv) := trivial
@[simp] theorem sort : ProjsOK ok (.sort u) := trivial
@[simp] theorem const : ProjsOK ok (.const c us) := trivial
@[simp] theorem lit : ProjsOK ok (.lit l) := trivial

theorem liftLooseBVars' {e : Expr} (H : ProjsOK ok e) (s d : Nat) :
    ProjsOK ok (e.liftLooseBVars' s d) := by
  induction e generalizing s <;> simp_all [Expr.liftLooseBVars']

theorem lowerLooseBVars' {e : Expr} (H : ProjsOK ok e) (s d : Nat) :
    ProjsOK ok (e.lowerLooseBVars' s d) := by
  induction e generalizing s <;> unfold Expr.lowerLooseBVars' <;> split <;> simp_all

theorem instantiate1' {e a : Expr} (H : ProjsOK ok e) (ha : ProjsOK ok a) (k : Nat) :
    ProjsOK ok (e.instantiate1' a k) := by
  induction e generalizing k <;> simp_all [Expr.instantiate1']
  case bvar i => split <;> [simp; split <;> [exact ha.liftLooseBVars' 0 k; simp]]

theorem instantiate1 {e a : Expr} (H : ProjsOK ok e) (ha : ProjsOK ok a) :
    ProjsOK ok (e.instantiate1 a) := by
  rw [Expr.instantiate1_eq]; exact H.instantiate1' ha 0

theorem instantiateList {e : Expr} {subst : List Expr} (H : ProjsOK ok e)
    (hs : ∀ a ∈ subst, ProjsOK ok a) (k : Nat) : ProjsOK ok (e.instantiateList subst k) := by
  induction subst generalizing e with
  | nil => exact H
  | cons a subst ih => exact ih (H.instantiate1' (hs a (.head _)) k) fun b hb => hs b (.tail _ hb)

theorem instantiateRevList {e : Expr} {subst : List Expr} (H : ProjsOK ok e)
    (hs : ∀ a ∈ subst, ProjsOK ok a) (k : Nat) : ProjsOK ok (e.instantiateRevList subst k) := by
  rw [← Expr.instantiateList_reverse]
  exact H.instantiateList (fun a ha => hs a (List.mem_reverse.1 ha)) k

theorem abstract1 {e : Expr} (H : ProjsOK ok e) (fv : FVarId) (k : Nat) :
    ProjsOK ok (e.abstract1 fv k) := by
  induction e generalizing k <;> simp_all [Expr.abstract1]
  case fvar => split <;> simp

theorem abstractN {e : Expr} (H : ProjsOK ok e) (xs : List FVarId) (k : Nat) :
    ProjsOK ok (e.abstractN xs k) := by
  induction e generalizing k <;> simp_all [Expr.abstractN]
  case fvar => split <;> simp

theorem mkAppList_iff {f : Expr} {args : List Expr} :
    ProjsOK ok (f.mkAppList args) ↔ ProjsOK ok f ∧ ∀ a ∈ args, ProjsOK ok a := by
  induction args generalizing f <;> simp_all [and_assoc]

theorem mkAppRevList_iff {f : Expr} {args : List Expr} :
    ProjsOK ok (f.mkAppRevList args) ↔ ProjsOK ok f ∧ ∀ a ∈ args, ProjsOK ok a := by
  rw [← Expr.mkAppList_reverse, mkAppList_iff]; simp

theorem getAppFn {e : Expr} (H : ProjsOK ok e) : ProjsOK ok e.getAppFn := by
  induction e <;> simp_all [Expr.getAppFn]

theorem of_mem_getAppArgsList {e a : Expr} (H : ProjsOK ok e) (ha : a ∈ e.getAppArgsList) :
    ProjsOK ok a := by
  rw [← e.mkAppList_getAppArgsList, mkAppList_iff] at H
  exact H.2 a ha

theorem getElem!_of_forall {args : Array Expr} (ha : ∀ a ∈ args, ProjsOK ok a) (i : Nat) :
    ProjsOK ok (args[i]!) := by
  by_cases h : i < args.size
  · rw [getElem!_pos args i h]; exact ha _ (Array.getElem_mem h)
  · rw [getElem!_neg args i h]; exact trivial

open private mkAppRangeAux from Lean.Expr in
theorem mkAppRange {f : Expr} {args : Array Expr} (hf : ProjsOK ok f)
    (ha : ∀ a ∈ args, ProjsOK ok a) : ProjsOK ok (mkAppRange f i j args) := by
  unfold Lean.mkAppRange
  suffices ∀ k i f, j - i = k → ProjsOK ok f →
      ProjsOK ok (mkAppRangeAux j args i f) from this _ _ _ rfl hf
  intro k; induction k with
  | zero => intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [omega; exact hf]
  | succ k ih =>
    intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [skip; exact hf]
    exact ih _ _ (by omega) ⟨hf, getElem!_of_forall ha _⟩

open private mkAppRevRangeAux from Lean.Expr in
theorem mkAppRevRange {f : Expr} {args : Array Expr} (hf : ProjsOK ok f)
    (ha : ∀ a ∈ args, ProjsOK ok a) : ProjsOK ok (mkAppRevRange f i j args) := by
  unfold Lean.Expr.mkAppRevRange
  suffices ∀ k j f, j - i = k → ProjsOK ok f →
      ProjsOK ok (mkAppRevRangeAux args i f j) from this _ _ _ rfl hf
  intro k; induction k with
  | zero => intro j f h hf; rw [mkAppRevRangeAux.eq_def]; split <;> [exact hf; omega]
  | succ k ih =>
    intro j f h hf; rw [mkAppRevRangeAux.eq_def]; split <;> [exact hf; skip]
    exact ih _ _ (by omega) ⟨hf, getElem!_of_forall ha _⟩

theorem instantiateLevelParamsCore' {e : Expr} (H : ProjsOK ok e) :
    ProjsOK ok (e.instantiateLevelParamsCore' red s) := by
  induction e <;> simp_all [Expr.instantiateLevelParamsCore']

theorem instantiateLevelParams {e : Expr} (H : ProjsOK ok e) :
    ProjsOK ok (e.instantiateLevelParams ps us) := by
  rw [Expr.instantiateLevelParams_eq]; exact H.instantiateLevelParamsCore'

theorem betaReduce {e e' : Expr} (B : BetaReduce e e') (H : ProjsOK ok e) : ProjsOK ok e' := by
  induction B with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih2 (ih1 H)
  | app _ ih => exact ⟨ih H.1, H.2⟩
  | beta => exact H.1.2.instantiate1' H.2 0

theorem natLitToConstructor : ProjsOK ok (Expr.natLitToConstructor n) := by
  cases n <;> simp [Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem strLitToConstructor : ProjsOK ok (Expr.strLitToConstructor s) := by
  simp only [Expr.strLitToConstructor, app_iff, const, true_and]
  induction s.toList <;> simp_all

theorem mono {ok' : Name → Prop} {e : Expr} (H : ProjsOK ok e) (h : ∀ s, ok s → ok' s) :
    ProjsOK ok' e := by
  induction e <;> simp_all

end ProjsOK

end Lean.Expr

namespace Lean.Expr

open Lean4Lean

/-! ### Application spines -/


@[simp] theorem getAppFn_getAppFn (e : Expr) : e.getAppFn.getAppFn = e.getAppFn := by
  induction e <;> simp_all [getAppFn]

theorem instantiateList_eq_self_of_closed {e : Expr} {L : List Expr} {k : Nat}
    (h : e.looseBVarRange' ≤ k) : e.instantiateList L k = e := by
  rw [← instantiateRevList_reverse]; exact instantiateRevList'_eq_self h

/-- With closed substitution values, `instantiateList L k` maps `bvar (k + m)` to `L[m]`. -/
theorem instantiateList_bvar_closed {L : List Expr} (hL : ∀ a ∈ L, a.looseBVarRange' = 0)
    (k m : Nat) (hm : m < L.length) : (Expr.bvar (k + m)).instantiateList L k = L[m] := by
  induction L generalizing m with
  | nil => simp at hm
  | cons a L ih =>
    cases m with
    | zero =>
      simp only [instantiateList, instantiate1', Nat.add_zero, Nat.lt_irrefl, if_false, if_true,
        List.getElem_cons_zero]
      rw [liftLooseBVars_eq_self (by simp [hL a (.head _)])]
      exact instantiateList_eq_self_of_closed (by simp [hL a (.head _)])
    | succ m =>
      simp only [instantiateList, instantiate1', List.getElem_cons_succ]
      rw [if_neg (by omega), if_neg (by omega), show k + (m + 1) - 1 = k + m by omega]
      exact ih (fun b hb => hL b (.tail _ hb)) m (by simpa using hm)

theorem _root_.Lean4Lean.BetaReduce.eq_of_getAppFn_const {e e' : Expr}
    (B : BetaReduce e e') (h : e.getAppFn = .const c us) : e' = e := by
  induction B with
  | refl => rfl
  | trans _ _ ih1 ih2 => have := ih1 h; subst this; exact ih2 h
  | app _ ih => rw [ih h]
  | beta => simp [getAppFn] at h

namespace ParamUniform

variable {heads : List Name} {params : List Expr} {ls : List Level}

theorem of_mem_getAppArgsList {e a : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (ha : a ∈ e.getAppArgsList) :
    ParamUniform heads params ls a := by
  by_cases hhit : ∃ c us, e.getAppFn = .const c us ∧ c ∈ heads
  · obtain ⟨c, us, hfn, hc⟩ := hhit
    obtain ⟨-, rest, hargs, hrest⟩ := H.getAppFn_const_head_inv hfn hc
    rw [hargs] at ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨fv, rfl⟩ := hp a ha; exact .fvar _
    · exact hrest a ha
  · rw [← e.mkAppList_getAppArgsList] at H
    refine (H.mkAppList_inv fun c us h hc => hhit ⟨c, us, ?_, hc⟩).2 a ha
    simpa using h

theorem getAppFn_of_not_head {e : Expr} (H : ParamUniform heads params ls e)
    (hnot : ∀ c us, e.getAppFn = .const c us → c ∉ heads) :
    ParamUniform heads params ls e.getAppFn := by
  rw [← e.mkAppList_getAppArgsList] at H
  exact (H.mkAppList_inv fun c us h => hnot c us (by simpa using h)).1

theorem getElem!_of_lt {args : Array Expr} (ha : ∀ a ∈ args, ParamUniform heads params ls a)
    {i : Nat} (h : i < args.size) : ParamUniform heads params ls (args[i]!) := by
  rw [getElem!_pos args i h]; exact ha _ (Array.getElem_mem h)

open private mkAppRangeAux from Lean.Expr in
/-- `mkAppRange f i j args` with `j ≤ args.size` reads only in-range arguments (so never the
default expression of an out-of-range `args[k]!`). -/
theorem mkAppRange {f : Expr} {args : Array Expr} (hj : j ≤ args.size)
    (hf : ParamUniform heads params ls f)
    (ha : ∀ a ∈ args, ParamUniform heads params ls a) :
    ParamUniform heads params ls (mkAppRange f i j args) := by
  unfold Lean.mkAppRange
  suffices ∀ k i f, j - i = k → ParamUniform heads params ls f →
      ParamUniform heads params ls (mkAppRangeAux j args i f) from this _ _ _ rfl hf
  intro k; induction k with
  | zero => intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [omega; exact hf]
  | succ k ih =>
    intro i f h hf; rw [mkAppRangeAux.eq_def]; split <;> [rename_i hij; exact hf]
    exact ih _ _ (by omega) (.app hf (getElem!_of_lt ha (by omega)))

open private mkAppRevRangeAux from Lean.Expr in
/-- `mkAppRevRange f i j args` with `j ≤ args.size` reads only in-range arguments. -/
theorem mkAppRevRange {f : Expr} {args : Array Expr} (hj : j ≤ args.size)
    (hf : ParamUniform heads params ls f)
    (ha : ∀ a ∈ args, ParamUniform heads params ls a) :
    ParamUniform heads params ls (mkAppRevRange f i j args) := by
  unfold Lean.Expr.mkAppRevRange
  suffices ∀ k j f, j - i = k → j ≤ args.size → ParamUniform heads params ls f →
      ParamUniform heads params ls (mkAppRevRangeAux args i f j) from this _ _ _ rfl hj hf
  intro k; induction k with
  | zero => intro j f h _ hf; rw [mkAppRevRangeAux.eq_def]; split <;> [exact hf; omega]
  | succ k ih =>
    intro j f h hj hf; rw [mkAppRevRangeAux.eq_def]; split <;> [exact hf; rename_i hij]
    exact ih _ _ (by omega) (by omega) (.app hf (getElem!_of_lt ha (by omega)))

theorem mkAppRevList {f : Expr} {args : List Expr} (hf : ParamUniform heads params ls f)
    (hargs : ∀ a ∈ args, ParamUniform heads params ls a) :
    ParamUniform heads params ls (f.mkAppRevList args) := by
  rw [← Expr.mkAppList_reverse]
  exact hf.mkAppList fun a ha => hargs a (List.mem_reverse.1 ha)

theorem betaReduce {e e' : Expr} (B : BetaReduce e e') (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) : ParamUniform heads params ls e' := by
  induction B with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih2 (ih1 H)
  | @app f f' a B ih =>
    by_cases hhit : ∃ c us, f.getAppFn = .const c us
    · obtain ⟨c, us, hfn⟩ := hhit
      rw [B.eq_of_getAppFn_const hfn]; exact H
    · have ⟨hf, ha⟩ := H.app_inv fun c us h _ => hhit ⟨c, us, h⟩
      exact .app (ih hf) ha
  | beta =>
    have ⟨hf, ha⟩ := H.app_inv fun c us h _ => by simp [getAppFn] at h
    exact hf.lam_inv.2.instantiate1' ha hp 0

theorem instantiateLevelParams_of_avoids {e : Expr} (H : e.AvoidsConsts heads) :
    ParamUniform heads params ls (e.instantiateLevelParams ps us) :=
  of_avoidsConsts H.instantiateLevelParams

end ParamUniform

/-! ### The bound-variable form -/

namespace ParamUniformBV

variable {heads : List Name} {ls : List Level}

theorem forallE_inv {n d : Nat} {nm : Name} {t b : Expr} {bi : BinderInfo}
    (H : ParamUniformBV heads n ls d (.forallE nm t b bi)) :
    ParamUniformBV heads n ls d t ∧ ParamUniformBV heads n ls (d + 1) b := by
  generalize he : Expr.forallE nm t b bi = e at H
  cases H with
  | forallE ht hb => cases he; exact ⟨ht, hb⟩
  | head =>
    have := congrArg Expr.getAppFn he
    rw [getAppFn_mkAppList_const] at this; simp [getAppFn] at this
  | _ => cases he

/-- A depth-`d` bound-variable form with zero parameters is a free-variable form with no
parameters. -/
theorem zero_params {d : Nat} {e : Expr} (H : ParamUniformBV heads 0 ls d e) :
    ParamUniform heads [] ls e := by
  induction H with
  | head hc => exact .head hc
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Instantiating a bound-variable-form term whose parameter block sits `d` binders out: the
closed substitution list `L` supplies `d` shaped values for the inner binders followed by the
parameters (in reverse, as `instantiateList` consumes the innermost binder first). -/
theorem instantiateList_params {n d : Nat} {As L : List Expr}
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv) (hn : As.length = n) (hlen : L.length = d + n)
    (hparam : ∀ i, i < n → L[d + (n - 1 - i)]? = As[i]?)
    (hL : ∀ a ∈ L, ParamUniform heads As ls a ∧ a.looseBVarRange' = 0) :
    ∀ {j k : Nat} {e : Expr}, ParamUniformBV heads n ls j e → j = d + k →
      ParamUniform heads As ls (e.instantiateList L k) := by
  intro j k e H hj
  have hS : ∀ a ∈ L, ParamUniform heads As ls a := fun a ha => (hL a ha).1
  have hC : ∀ a ∈ L, a.looseBVarRange' = 0 := fun a ha => (hL a ha).2
  induction H generalizing k with
  | @head c j hc =>
    have hg : ∀ f a : Expr, (Expr.app f a).instantiateList L k =
        .app (f.instantiateList L k) (a.instantiateList L k) := fun _ _ => instantiateList_app
    have hmap : ∀ (f : Expr) (l : List Expr),
        (f.mkAppList l).instantiateList L k =
          (f.instantiateList L k).mkAppList (l.map (·.instantiateList L k)) := by
      intro f l
      induction l generalizing f with
      | nil => rfl
      | cons a l ih => simp only [Expr.mkAppList, List.map_cons]; rw [ih, hg]
    rw [hmap, instantiateList_eq_self_of_closed (by simp [looseBVarRange'])]
    have : (paramBVars n j).map (·.instantiateList L k) = As := by
      refine List.ext_getElem (by simp [hn]) fun i h1 h2 => ?_
      have hi : i < n := by simpa using h1
      simp only [paramBVars, List.map_map, List.getElem_map, List.getElem_range,
        Function.comp_apply]
      rw [hj, show d + k + (n - 1 - i) = k + (d + (n - 1 - i)) by omega,
        instantiateList_bvar_closed hC k _ (by omega)]
      have := hparam i hi
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem h2] at this
      exact Option.some.inj this
    rw [this]; exact .head hc
  | app _ _ ihf iha => rw [instantiateList_app]; exact .app (ihf hj) (iha hj)
  | const hc => exact (ParamUniform.const hc).instantiateList hS hAs k
  | bvar i => exact (ParamUniform.bvar i).instantiateList hS hAs k
  | fvar fv => exact (ParamUniform.fvar fv).instantiateList hS hAs k
  | mvar mv => exact (ParamUniform.mvar mv).instantiateList hS hAs k
  | sort u => exact (ParamUniform.sort u).instantiateList hS hAs k
  | lit l => exact (ParamUniform.lit l).instantiateList hS hAs k
  | lam _ _ iht ihb =>
    rw [instantiateList_lam]; exact .lam (iht hj) (ihb (k := k + 1) (by omega))
  | forallE _ _ iht ihb =>
    rw [instantiateList_forallE]; exact .forallE (iht hj) (ihb (k := k + 1) (by omega))
  | letE _ _ _ iht ihv ihb =>
    rw [instantiateList_letE]; exact .letE (iht hj) (ihv hj) (ihb (k := k + 1) (by omega))
  | mdata _ ih =>
    rw [← instantiateRevList_reverse, instantiateRevList_mdata, instantiateRevList_reverse]
    exact .mdata (ih hj)
  | proj _ ih =>
    rw [← instantiateRevList_reverse, instantiateRevList_proj, instantiateRevList_reverse]
    exact .proj (ih hj)

end ParamUniformBV

/-! ### Remaining parameter telescopes -/

/-- `HeadRest heads n ls k t`: `t` is what remains of the type of a head constant (a forall
telescope of `n` parameters around a bound-variable-form body) after `k` of its binders have been
walked: either still inside the parameter telescope, or in the body at depth `k - n`. -/
def HeadRest (heads : List Name) (n : Nat) (ls : List Level) (k : Nat) (t : Expr) : Prop :=
  (k ≤ n ∧ ∃ body, LeadingForalls (n - k) t body ∧ ParamUniformBV heads n ls 0 body) ∨
  (n ≤ k ∧ ParamUniformBV heads n ls (k - n) t)

namespace HeadRest

variable {heads : List Name} {n : Nat} {ls : List Level}

theorem start {t body : Expr} (H1 : LeadingForalls n t body) (H2 : ParamUniformBV heads n ls 0 body) :
    HeadRest heads n ls 0 t := .inl ⟨Nat.zero_le _, body, by simpa using H1, H2⟩

theorem forallE {k : Nat} {nm : Name} {t b : Expr} {bi : BinderInfo}
    (H : HeadRest heads n ls k (.forallE nm t b bi)) : HeadRest heads n ls (k + 1) b := by
  rcases H with ⟨hk, body, H1, H2⟩ | ⟨hk, H⟩
  · by_cases hlt : k < n
    · refine .inl ⟨hlt, body, ?_, H2⟩
      rw [show n - k = (n - (k + 1)) + 1 by omega] at H1
      exact H1.forallE_inv
    · have hkn : k = n := by omega
      subst hkn
      rw [Nat.sub_self] at H1
      cases H1
      exact .inr ⟨by omega, by simpa using H2.forallE_inv.2⟩
  · refine .inr ⟨by omega, ?_⟩
    rw [show k + 1 - n = k - n + 1 by omega]
    exact H.forallE_inv.2

theorem body {k : Nat} {t : Expr} (H : HeadRest heads n ls k t) (hk : n ≤ k) :
    ParamUniformBV heads n ls (k - n) t := by
  rcases H with ⟨hk', body, H1, H2⟩ | ⟨_, H⟩
  · have : k = n := by omega
    subst this; rw [Nat.sub_self] at H1 ⊢; cases H1; exact H2
  · exact H

theorem isForall {k : Nat} {t : Expr} (H : HeadRest heads n ls k t) (hk : k < n) :
    ∃ nm d b bi, t = .forallE nm d b bi := by
  rcases H with ⟨-, body, H1, -⟩ | ⟨hk', -⟩
  · rw [show n - k = (n - k - 1) + 1 by omega] at H1
    obtain ⟨nm, d, b, bi, rfl, -⟩ := H1.isForall
    exact ⟨_, _, _, _, rfl⟩
  · omega

end HeadRest

end Lean.Expr

namespace Lean4Lean
open Lean

/-! ### The environment condition -/

/-- Names of the primitive constants that the checker builds on its own: the literal type `Nat`,
the constructors of `Nat` literal expansion, the heads `String.ofList` and `Char.ofNat` of string
literal expansion, and the boolean results of `Nat` predicates. All of them are reserved
(`Kernel.Environment.primitives`), so an ordinary declaration never introduces them. -/
def checkerPrimNames : List Name :=
  [``Nat, ``Nat.zero, ``Nat.succ, ``String.ofList, ``Char.ofNat, ``Bool.true, ``Bool.false]

/-- The other constants of string literals: the literal type `String` and the constants `Char`,
`List.nil`, `List.cons` of the expansion. They are not reserved, but they are only produced from a
string literal, which only translates when `Char.ofNat` and `String.ofList` exist
(`VEnv.ContainsLits`). -/
def strLitNames : List Name := [``String, ``Char, ``List.nil, ``List.cons]

/-- The environment supports string literals: `Char.ofNat` and `String.ofList` are declared (the
kernel-environment form of `VEnv.ContainsLits (.strVal _)`). -/
def StrLitsDeclared (env : Lean.Kernel.Environment) : Prop :=
  (∃ ci, env.find? ``Char.ofNat = some ci) ∧ ∃ ci, env.find? ``String.ofList = some ci

/-- A projection on the structure `s` is compatible with the head set: neither `s` nor any
constructor of `s` is a head. (Lowering never renames projections, so projections on auxiliary
families do not occur; projections on a source family whose constructor mentions an auxiliary
family would produce field types at arbitrary parameters.) -/
def projAvoidsHeads (env : Lean.Kernel.Environment) (heads : List Name) (s : Name) : Prop :=
  s ∉ heads ∧ ∀ v, env.find? s = some (.inductInfo v) → ∀ c ∈ v.ctors, c ∉ heads

/-- The type of a head constant (instantiated at the levels `ls`): a forall telescope of `nparams`
parameters around a parameter-uniform body in bound-variable form. -/
def HeadType (heads : List Name) (nparams : Nat) (ls : List Level) (t : Expr) : Prop :=
  ∃ body, t.LeadingForalls nparams body ∧ Expr.ParamUniformBV heads nparams ls 0 body

/-- The environment condition of the parameter-uniformity invariant, for the head set `heads` (in the
nested-inductive application: the auxiliary families, their constructors, and the constructors
of the source families), `nparams` parameters and block levels `ls`.

* Every constant outside `heads`, every definition value and every recursor rule mentions no
  head.
* Heads are inductive families or constructors, and their types at
  the levels `ls` are parameter telescopes around parameter-uniform bodies in bound-variable form.
* No recursor eliminates a head family or a family with a head constructor (the K-like and
  structure-eta expansions build constructor applications from the major premise's type).
* Projection nodes in the environment respect `projAvoidsHeads` (no projections on heads or on
  families with head constructors).
* The constants that the checker introduces itself are not heads: the reserved ones
  (`checkerPrimNames`) always, the remaining constants of string literals (`strLitNames`) as soon as
  the environment supports string literals (`StrLitsDeclared`), which is the only situation in
  which the checker produces them. -/
structure EnvParamUniform (env : Lean.Kernel.Environment) (heads : List Name) (nparams : Nat)
    (ls : List Level) : Prop where
  prims : ∀ n ∈ checkerPrimNames, n ∉ heads
  strs : StrLitsDeclared env → ∀ n ∈ strLitNames, n ∉ heads
  type_avoids : ∀ {n ci}, env.find? n = some ci → n ∉ heads → ci.type.AvoidsConsts heads
  value_avoids : ∀ {n ci v}, env.find? n = some ci → ci.deltaValue? = some v →
    v.AvoidsConsts heads
  rules_avoid : ∀ {n r}, env.find? n = some (.recInfo r) → ∀ rule ∈ r.rules,
    rule.rhs.AvoidsConsts heads
  head_kind : ∀ {n ci}, env.find? n = some ci → n ∈ heads →
    (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v)
  head_type : ∀ {n ci}, env.find? n = some ci → n ∈ heads →
    HeadType heads nparams ls (ci.instantiateTypeLevelParams ls)
  rec_major : ∀ {n r}, env.find? n = some (.recInfo r) → r.getMajorInduct ∉ heads ∧
    ∀ v, env.find? r.getMajorInduct = some (.inductInfo v) → ∀ c ∈ v.ctors, c ∉ heads
  type_projs : ∀ {n ci}, env.find? n = some ci → ci.type.ProjsOK (projAvoidsHeads env heads)
  value_projs : ∀ {n ci v}, env.find? n = some ci → ci.deltaValue? = some v →
    v.ProjsOK (projAvoidsHeads env heads)
  rules_projs : ∀ {n r}, env.find? n = some (.recInfo r) → ∀ rule ∈ r.rules,
    rule.rhs.ProjsOK (projAvoidsHeads env heads)

theorem EnvParamUniform.prim {env heads nparams ls} (H : EnvParamUniform env heads nparams ls)
    {n : Name} (h : n ∈ checkerPrimNames := by simp [checkerPrimNames]) : n ∉ heads := H.prims n h

theorem EnvParamUniform.str {env heads nparams ls} (H : EnvParamUniform env heads nparams ls)
    (hs : StrLitsDeclared env) {n : Name} (h : n ∈ strLitNames := by simp [strLitNames]) :
    n ∉ heads := H.strs hs n h

end Lean4Lean

namespace Lean.Expr
open Lean4Lean

/-! ### The combined predicate -/

/-- Parameter uniformity together with the projection condition: the predicate the type checker
preserves. -/
def ParamUniformIn (env : Lean.Kernel.Environment) (heads : List Name) (As : List Expr) (ls : List Level)
    (e : Expr) : Prop :=
  e.ParamUniform heads As ls ∧ e.ProjsOK (projAvoidsHeads env heads)

namespace ParamUniformIn

variable {env : Lean.Kernel.Environment} {heads : List Name} {As : List Expr} {ls : List Level}

theorem fvar : ParamUniformIn env heads As ls (.fvar fv) := ⟨.fvar _, trivial⟩
theorem sort : ParamUniformIn env heads As ls (.sort u) := ⟨.sort _, trivial⟩
theorem lit : ParamUniformIn env heads As ls (.lit l) := ⟨.lit _, trivial⟩
theorem const (h : c ∉ heads) : ParamUniformIn env heads As ls (.const c us) := ⟨.const h, trivial⟩

theorem app (hf : ParamUniformIn env heads As ls f) (ha : ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (.app f a) := ⟨.app hf.1 ha.1, hf.2, ha.2⟩
theorem forallE (ht : ParamUniformIn env heads As ls t) (hb : ParamUniformIn env heads As ls b) :
    ParamUniformIn env heads As ls (.forallE n t b bi) := ⟨.forallE ht.1 hb.1, ht.2, hb.2⟩
theorem letE (ht : ParamUniformIn env heads As ls t) (hv : ParamUniformIn env heads As ls v)
    (hb : ParamUniformIn env heads As ls b) : ParamUniformIn env heads As ls (.letE n t v b nd) :=
  ⟨.letE ht.1 hv.1 hb.1, ht.2, hv.2, hb.2⟩
theorem proj (hs : projAvoidsHeads env heads s) (h : ParamUniformIn env heads As ls e) :
    ParamUniformIn env heads As ls (.proj s i e) := ⟨.proj h.1, hs, h.2⟩

theorem lam_inv (H : ParamUniformIn env heads As ls (.lam n t b bi)) :
    ParamUniformIn env heads As ls t ∧ ParamUniformIn env heads As ls b :=
  ⟨⟨H.1.lam_inv.1, H.2.1⟩, ⟨H.1.lam_inv.2, H.2.2⟩⟩
theorem forallE_inv (H : ParamUniformIn env heads As ls (.forallE n t b bi)) :
    ParamUniformIn env heads As ls t ∧ ParamUniformIn env heads As ls b :=
  ⟨⟨H.1.forallE_inv.1, H.2.1⟩, ⟨H.1.forallE_inv.2, H.2.2⟩⟩
theorem letE_inv (H : ParamUniformIn env heads As ls (.letE n t v b nd)) :
    ParamUniformIn env heads As ls t ∧ ParamUniformIn env heads As ls v ∧ ParamUniformIn env heads As ls b :=
  ⟨⟨H.1.letE_inv.1, H.2.1⟩, ⟨H.1.letE_inv.2.1, H.2.2.1⟩, ⟨H.1.letE_inv.2.2, H.2.2.2⟩⟩
theorem mdata_inv (H : ParamUniformIn env heads As ls (.mdata m e)) : ParamUniformIn env heads As ls e :=
  ⟨H.1.mdata_inv, H.2⟩
theorem proj_inv (H : ParamUniformIn env heads As ls (.proj s i e)) :
    projAvoidsHeads env heads s ∧ ParamUniformIn env heads As ls e := ⟨H.2.1, H.1.proj_inv, H.2.2⟩

variable (hp : ∀ p ∈ As, ∃ fv, p = .fvar fv)
include hp

theorem instantiate1' (H : ParamUniformIn env heads As ls e) (ha : ParamUniformIn env heads As ls a) (k : Nat) :
    ParamUniformIn env heads As ls (e.instantiate1' a k) :=
  ⟨H.1.instantiate1' ha.1 hp k, H.2.instantiate1' ha.2 k⟩

theorem instantiate1 (H : ParamUniformIn env heads As ls e) (ha : ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (e.instantiate1 a) :=
  ⟨H.1.instantiate1 ha.1 hp, H.2.instantiate1 ha.2⟩

theorem instantiateList {subst : List Expr} (H : ParamUniformIn env heads As ls e)
    (hs : ∀ a ∈ subst, ParamUniformIn env heads As ls a) (k : Nat) :
    ParamUniformIn env heads As ls (e.instantiateList subst k) :=
  ⟨H.1.instantiateList (fun a h => (hs a h).1) hp k, H.2.instantiateList (fun a h => (hs a h).2) k⟩

theorem of_mem_getAppArgsList (H : ParamUniformIn env heads As ls e) (ha : a ∈ e.getAppArgsList) :
    ParamUniformIn env heads As ls a :=
  ⟨H.1.of_mem_getAppArgsList hp ha, H.2.of_mem_getAppArgsList ha⟩

theorem of_mem_getAppArgs (H : ParamUniformIn env heads As ls e) (ha : a ∈ e.getAppArgs) :
    ParamUniformIn env heads As ls a :=
  H.of_mem_getAppArgsList hp (by rw [← getAppArgs_toList]; exact Array.mem_toList_iff.2 ha)

theorem of_mem_getAppArgsRevList (H : ParamUniformIn env heads As ls e)
    (ha : a ∈ e.getAppArgsRevList) : ParamUniformIn env heads As ls a :=
  H.of_mem_getAppArgsList hp (by rw [← getAppArgsRevList_reverse]; exact List.mem_reverse.2 ha)

theorem betaReduce (B : BetaReduce e e') (H : ParamUniformIn env heads As ls e) :
    ParamUniformIn env heads As ls e' := ⟨H.1.betaReduce B hp, H.2.betaReduce B⟩

omit hp in
theorem getAppFn_of_not_head (H : ParamUniformIn env heads As ls e)
    (hnot : ∀ c us, e.getAppFn = .const c us → c ∉ heads) :
    ParamUniformIn env heads As ls e.getAppFn := ⟨H.1.getAppFn_of_not_head hnot, H.2.getAppFn⟩

omit hp in
theorem mkAppList (hf : ParamUniformIn env heads As ls f) (hargs : ∀ a ∈ args, ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (f.mkAppList args) :=
  ⟨hf.1.mkAppList fun a h => (hargs a h).1, ProjsOK.mkAppList_iff.2 ⟨hf.2, fun a h => (hargs a h).2⟩⟩

omit hp in
theorem mkAppRevList (hf : ParamUniformIn env heads As ls f)
    (hargs : ∀ a ∈ args, ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (f.mkAppRevList args) :=
  ⟨hf.1.mkAppRevList fun a h => (hargs a h).1,
    ProjsOK.mkAppRevList_iff.2 ⟨hf.2, fun a h => (hargs a h).2⟩⟩

omit hp in
theorem mkAppRange {args : Array Expr} (hj : j ≤ args.size)
    (hf : ParamUniformIn env heads As ls f) (hargs : ∀ a ∈ args, ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (Lean.mkAppRange f i j args) :=
  ⟨hf.1.mkAppRange hj fun a h => (hargs a h).1, hf.2.mkAppRange fun a h => (hargs a h).2⟩

omit hp in
theorem mkAppRevRange {args : Array Expr} (hj : j ≤ args.size)
    (hf : ParamUniformIn env heads As ls f) (hargs : ∀ a ∈ args, ParamUniformIn env heads As ls a) :
    ParamUniformIn env heads As ls (f.mkAppRevRange i j args) :=
  ⟨hf.1.mkAppRevRange hj fun a h => (hargs a h).1, hf.2.mkAppRevRange fun a h => (hargs a h).2⟩

omit hp in
theorem of_avoids {e : Expr} (H : e.AvoidsConsts heads) (hp : e.ProjsOK (projAvoidsHeads env heads)) :
    ParamUniformIn env heads As ls e := ⟨.of_avoidsConsts H, hp⟩

omit hp in
theorem instantiateLevelParams_of_avoids {e : Expr} (H : e.AvoidsConsts heads)
    (hp : e.ProjsOK (projAvoidsHeads env heads)) :
    ParamUniformIn env heads As ls (e.instantiateLevelParams ps us) :=
  ⟨.instantiateLevelParams_of_avoids H, hp.instantiateLevelParams⟩

end ParamUniformIn

end Lean.Expr

namespace Lean.Expr
open Lean4Lean

/-! ### Invariance under `==`

Non-strict `Expr` equality ignores binder names and binder infos only. -/

theorem eqv_app_iff' {e f a : Expr} :
    (e == .app f a) = true ↔ ∃ f' a', e = .app f' a' ∧ (f' == f) = true ∧ (a' == a) = true := by
  cases e <;> simp [(· == ·), Expr.eqv']
  exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h3⟩ => h1 ▸ h2 ▸ h3⟩

theorem eqv_fvar_iff' {e : Expr} : (e == .fvar fv) = true ↔ e = .fvar fv := by
  constructor
  · intro h
    cases e <;> simp [(· == ·), Expr.eqv'] at h
    exact congrArg Expr.fvar (LawfulBEq.eq_of_beq h)
  · rintro rfl; exact eqv_refl _

theorem eqv_mkAppRevList_fvars {e f : Expr} {params : List Expr}
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (hf : ∀ e', (e' == f) = true → e' = f)
    (h : (e == f.mkAppRevList params) = true) : e = f.mkAppRevList params := by
  induction params generalizing e with
  | nil => exact hf e h
  | cons a l ih =>
    obtain ⟨f', a', rfl, h1, h2⟩ := eqv_app_iff'.1 h
    obtain ⟨fv, rfl⟩ := hp a (.head _)
    rw [ih (fun p hp' => hp p (.tail _ hp')) h1, eqv_fvar_iff'.1 h2]; rfl

theorem eqv_mkAppList_fvars {e f : Expr} {params : List Expr}
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (hf : ∀ e', (e' == f) = true → e' = f)
    (h : (e == f.mkAppList params) = true) : e = f.mkAppList params := by
  rw [← Expr.mkAppRevList_reverse] at h ⊢
  exact eqv_mkAppRevList_fvars (fun p h' => hp p (List.mem_reverse.1 h')) hf h

theorem ProjsOK.eqv {ok : Name → Prop} {e e' : Expr} (h : (e == e') = true)
    (H : ProjsOK ok e) : ProjsOK ok e' := by
  simp [(· == ·)] at h
  induction e generalizing e' <;> (cases e' <;> try change false = _ at h; cases h)
  all_goals simp [Expr.eqv'] at h; simp_all

theorem ParamUniform.eqv {heads : List Name} {params : List Expr} {ls : List Level} {e e' : Expr}
    (H : ParamUniform heads params ls e) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (h : (e' == e) = true) : ParamUniform heads params ls e' := by
  induction H generalizing e' with
  | head hc =>
    rw [eqv_mkAppList_fvars hp (fun e' h' => eqv_const.1 h') h]; exact .head hc
  | app _ _ ihf iha =>
    obtain ⟨f', a', rfl, h1, h2⟩ := eqv_app_iff'.1 h
    exact .app (ihf h1) (iha h2)
  | const hc => rw [eqv_const.1 h]; exact .const hc
  | bvar => cases e' <;> simp [(· == ·), Expr.eqv'] at h; exact .bvar _
  | fvar => rw [eqv_fvar_iff'.1 h]; exact .fvar _
  | mvar => cases e' <;> simp [(· == ·), Expr.eqv'] at h; exact .mvar _
  | sort => rw [eqv_sort.1 h]; exact .sort _
  | lit => cases e' <;> simp [(· == ·), Expr.eqv'] at h; exact .lit _
  | lam _ _ iht ihb =>
    cases e' <;> simp [(· == ·), Expr.eqv'] at h
    exact .lam (iht (by simp [(· == ·), h.1])) (ihb (by simp [(· == ·), h.2]))
  | forallE _ _ iht ihb =>
    cases e' <;> simp [(· == ·), Expr.eqv'] at h
    exact .forallE (iht (by simp [(· == ·), h.1])) (ihb (by simp [(· == ·), h.2]))
  | letE _ _ _ iht ihv ihb =>
    cases e' <;> simp [(· == ·), Expr.eqv'] at h
    exact .letE (iht (by simp [(· == ·), h.1.1.1])) (ihv (by simp [(· == ·), h.1.1.2]))
      (ihb (by simp [(· == ·), h.1.2]))
  | mdata _ ih =>
    cases e' <;> simp [(· == ·), Expr.eqv'] at h
    exact .mdata (ih (by simp [(· == ·), h.1]))
  | proj _ ih =>
    cases e' <;> simp [(· == ·), Expr.eqv'] at h
    obtain ⟨h1, rfl, rfl⟩ := h
    exact .proj (ih (by simp [(· == ·), h1]))

theorem ParamUniformIn.eqv {env : Lean.Kernel.Environment} {heads : List Name} {As : List Expr}
    {ls : List Level} {e e' : Expr} (H : ParamUniformIn env heads As ls e)
    (hp : ∀ p ∈ As, ∃ fv, p = .fvar fv) (h : (e == e') = true) : ParamUniformIn env heads As ls e' :=
  ⟨H.1.eqv hp (BEq.symm h), H.2.eqv h⟩

end Lean.Expr

namespace Lean.Expr
open Lean4Lean
theorem IsNatResult.paramUniformIn {env : Lean.Kernel.Environment} {heads : List Name} {As : List Expr}
    {ls : List Level} {nparams} (H : EnvParamUniform env heads nparams ls) {e : Expr}
    (h : IsNatResult e) : e.ParamUniformIn env heads As ls := by
  rcases h with ⟨n, rfl⟩ | rfl | rfl
  · exact .lit
  · exact .const H.prim
  · exact .const H.prim

end Lean.Expr

namespace Lean.Expr.ParamUniformIn
open Lean4Lean

variable {env : Lean.Kernel.Environment} {heads : List Name} {As : List Expr} {ls : List Level}

theorem natLitToConstructor {nparams} (H : EnvParamUniform env heads nparams ls) :
    (Expr.natLitToConstructor n).ParamUniformIn env heads As ls := by
  cases n with
  | zero => exact .const H.prim
  | succ n => exact .app (.const H.prim) .lit

theorem strLitToConstructor {nparams} (H : EnvParamUniform env heads nparams ls)
    (hs : StrLitsDeclared env) : (Expr.strLitToConstructor s).ParamUniformIn env heads As ls := by
  simp only [Expr.strLitToConstructor]
  refine .app (.const H.prim) ?_
  induction s.toList with
  | nil => exact .app (.const (H.str hs)) (.const (H.str hs))
  | cons a l ih =>
    exact .app (.app (.app (.const (H.str hs)) (.const (H.str hs))) (.app (.const H.prim) .lit))
      ih

end Lean.Expr.ParamUniformIn

namespace Lean.Expr
open Lean4Lean

theorem ParamUniform.abstract1 {heads : List Name} {params : List Expr} {ls : List Level} {e : Expr}
    (H : ParamUniform heads params ls e) {fv : FVarId}
    (hp : ∀ p ∈ params, ∃ fv', p = .fvar fv' ∧ fv' ≠ fv) (k : Nat) :
    ParamUniform heads params ls (e.abstract1 fv k) := by
  induction H generalizing k with
  | @head c hc =>
    have hmap : ∀ (f : Expr) (l : List Expr),
        (f.mkAppList l).abstract1 fv k = (f.abstract1 fv k).mkAppList (l.map (·.abstract1 fv k)) := by
      intro f l
      induction l generalizing f with
      | nil => rfl
      | cons a l ih => simp only [Expr.mkAppList, List.map_cons]; rw [ih]; rfl
    rw [hmap]
    have : params.map (·.abstract1 fv k) = params := by
      conv => rhs; rw [← List.map_id params]
      refine List.map_congr_left fun p hmem => ?_
      obtain ⟨fv', rfl, hne⟩ := hp p hmem
      simp [Expr.abstract1, Ne.symm hne]
    rw [this]; exact .head hc
  | app _ _ ihf iha => exact .app (ihf k) (iha k)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar fv' => simp only [Expr.abstract1]; split <;> [exact .bvar _; exact .fvar _]
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht k) (ihb (k + 1))
  | forallE _ _ iht ihb => exact .forallE (iht k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht k) (ihv k) (ihb (k + 1))
  | mdata _ ih => exact .mdata (ih k)
  | proj _ ih => exact .proj (ih k)

namespace ParamUniformIn

variable {env : Lean.Kernel.Environment} {heads : List Name} {As : List Expr} {ls : List Level}

theorem abstract1 {e : Expr} (H : ParamUniformIn env heads As ls e) {fv : FVarId}
    (hp : ∀ p ∈ As, ∃ fv', p = .fvar fv' ∧ fv' ≠ fv) (k : Nat) :
    ParamUniformIn env heads As ls (e.abstract1 fv k) := ⟨H.1.abstract1 hp k, H.2.abstract1 fv k⟩

theorem lowerLooseBVars' {e : Expr} (H : ParamUniformIn env heads As ls e)
    (hp : ∀ p ∈ As, ∃ fv, p = .fvar fv) (s d : Nat) :
    ParamUniformIn env heads As ls (e.lowerLooseBVars' s d) :=
  ⟨H.1.lowerLooseBVars' hp s d, H.2.lowerLooseBVars' s d⟩

end ParamUniformIn

end Lean.Expr

namespace Lean.Expr
open Lean4Lean


theorem getAppArgsList_mkAppRevList (f : Expr) (l : List Expr) :
    (f.mkAppRevList l).getAppArgsList = f.getAppArgsList ++ l.reverse := by
  rw [← mkAppList_reverse, getAppArgsList_mkAppList]

theorem getAppFn_mkAppRevList (f : Expr) (l : List Expr) :
    (f.mkAppRevList l).getAppFn = f.getAppFn := by
  rw [← mkAppList_reverse, getAppFn_mkAppList]

end Lean.Expr
