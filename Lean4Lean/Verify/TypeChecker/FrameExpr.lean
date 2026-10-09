import Lean4Lean.Verify.TypeChecker.FrameBasic
import Lean4Lean.Verify.Inductive.Recursor.Binders.ParameterPrefixes
import Lean4Lean.Verify.TypeChecker.Basic

/-!
# Frame lemma: ghost-freeness of expression operations

`GhostFree G` is preserved by every pure expression operation the checker applies to its inputs.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

/-- Every element of the array is ghost-free. -/
def GhostFreeArr (G : FVarId → Prop) (arr : Array Expr) : Prop := ∀ a ∈ arr, GhostFree G a

theorem GhostFree.default : GhostFree G (default : Expr) := FVarsIn.default

theorem GhostFree.panic : GhostFree G (panicWithPosWithDecl m d l c msg : Expr) := by
  simp only [panicWithPosWithDecl]; exact GhostFree.default

theorem GhostFreeArr.getElem! {arr : Array Expr} (h : GhostFreeArr G arr) (i : Nat) : GhostFree G arr[i]! := by
  rw [Array.getElem!_eq_getD]; unfold Array.getD; split
  · exact h _ (Array.getElem_mem _)
  · exact GhostFree.default

theorem GhostFreeArr.getElem? {arr : Array Expr} (h : GhostFreeArr G arr) {i : Nat} {a : Expr}
    (e : arr[i]? = some a) : GhostFree G a :=
  h _ (Array.mem_of_getElem? e)

theorem GhostFreeArr.getElem {arr : Array Expr} (h : GhostFreeArr G arr) {i : Nat} (hi : i < arr.size) :
    GhostFree G arr[i] := h _ (Array.getElem_mem _)

theorem GhostFreeArr.empty : GhostFreeArr G #[] := nofun

theorem GhostFreeArr.push {arr : Array Expr} (h : GhostFreeArr G arr) (ha : GhostFree G a) :
    GhostFreeArr G (arr.push a) := by
  intro x hx; rcases Array.mem_push.1 hx with hx | rfl
  · exact h _ hx
  · exact ha

theorem GhostFreeArr.reverse {arr : Array Expr} (h : GhostFreeArr G arr) : GhostFreeArr G arr.reverse :=
  fun _ hx => h _ (Array.mem_reverse.1 hx)

theorem GhostFreeArr.extract {arr : Array Expr} (h : GhostFreeArr G arr) : GhostFreeArr G (arr.extract i j) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hx
  exact h _ (Array.getElem_mem _)

open private mkAppRangeAux from Lean.Expr in
theorem GhostFree.mkAppRange {arr : Array Expr} (hf : GhostFree G f) (h : GhostFreeArr G arr) :
    GhostFree G (mkAppRange f i j arr) := by
  unfold Lean.mkAppRange
  generalize hk : j - i = k
  induction k generalizing i f with
  | zero => rw [mkAppRangeAux, if_neg (by omega)]; exact hf
  | succ k ih => rw [mkAppRangeAux, if_pos (by omega)]; exact ih ⟨hf, h.getElem! i⟩ (by omega)

open private mkAppRevRangeAux from Lean.Expr in
theorem GhostFree.mkAppRevRange {arr : Array Expr} (hf : GhostFree G f) (h : GhostFreeArr G arr) :
    GhostFree G (f.mkAppRevRange i j arr) := by
  unfold Expr.mkAppRevRange
  induction j generalizing f with
  | zero => rw [mkAppRevRangeAux, if_pos (Nat.zero_le _)]; exact hf
  | succ j ih =>
    rw [mkAppRevRangeAux]; split
    · exact hf
    · exact ih ⟨hf, h.getElem! _⟩

theorem GhostFree.getAppFn : ∀ {e : Expr}, GhostFree G e → GhostFree G e.getAppFn
  | .app f _, h => GhostFree.getAppFn (e := f) h.1
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h
  | .lam .., h | .forallE .., h | .letE .., h | .lit .., h | .mdata .., h | .proj .., h => h

theorem GhostFree.getAppArgsRevList {e : Expr} (h : GhostFree G e) : ∀ a ∈ e.getAppArgsRevList, GhostFree G a := by
  induction e <;> simp [Expr.getAppArgsRevList]
  rename_i ih _; exact ⟨h.2, ih h.1⟩

theorem GhostFree.getAppArgs (h : GhostFree G e) : GhostFreeArr G e.getAppArgs := by
  rw [Expr.getAppArgs_eq_rev]; intro a ha
  exact GhostFree.getAppArgsRevList h a (by simpa using ha)

theorem GhostFree.getAppRevArgs (h : GhostFree G e) : GhostFreeArr G e.getAppRevArgs := by
  rw [Expr.getAppRevArgs_eq]; intro a ha
  exact GhostFree.getAppArgsRevList h a (by simpa using ha)

theorem GhostFree.appArg! : ∀ {e : Expr}, GhostFree G e → GhostFree G e.appArg!
  | .app .., h => h.2
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .lam .., _ | .forallE .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.appArg!] using GhostFree.default

theorem GhostFree.bindingBody! : ∀ {e : Expr}, GhostFree G e → GhostFree G e.bindingBody!
  | .lam .., h | .forallE .., h => h.2
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .app .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.bindingBody!] using GhostFree.default

theorem GhostFree.bindingDomain! : ∀ {e : Expr}, GhostFree G e → GhostFree G e.bindingDomain!
  | .lam .., h | .forallE .., h => h.1
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .app .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.bindingDomain!] using GhostFree.default

theorem GhostFree.instantiate1 (h1 : GhostFree G e) (h2 : GhostFree G a) : GhostFree G (e.instantiate1 a) := by
  rw [Expr.instantiate1_eq]; exact FVarsIn.instantiate1 h1 h2

theorem GhostFree.instantiate {arr : Array Expr} (h1 : GhostFree G e) (h2 : GhostFreeArr G arr) :
    GhostFree G (e.instantiate arr) := by
  rw [Expr.instantiate_eq]; exact FVarsIn.instantiateList h1 fun a ha => h2 a (by simpa using ha)

theorem GhostFree.instantiateRev {arr : Array Expr} (h1 : GhostFree G e) (h2 : GhostFreeArr G arr) :
    GhostFree G (e.instantiateRev arr) := by
  rw [Expr.instantiateRev_eq]; exact h1.instantiate h2.reverse

theorem GhostFree.instantiateRange {arr : Array Expr} (h1 : GhostFree G e) (h2 : GhostFreeArr G arr) :
    GhostFree G (e.instantiateRange i j arr) := by
  rw [Expr.instantiateRange_eq]; exact h1.instantiate h2.extract

theorem GhostFree.instantiateRevRange {arr : Array Expr} (h1 : GhostFree G e) (h2 : GhostFreeArr G arr) :
    GhostFree G (e.instantiateRevRange i j arr) := by
  rw [Expr.instantiateRevRange_eq]; exact h1.instantiateRev h2.extract

theorem GhostFree.abstractN (h : GhostFree G e) : GhostFree G (e.abstractN xs k) := by
  induction e generalizing k <;> simp_all [Expr.abstractN, FVarsIn]
  split <;> simp_all [FVarsIn]

theorem GhostFree.lowerLooseBVars' (h : GhostFree G e) : GhostFree G (e.lowerLooseBVars' s d) := by
  induction e generalizing s <;> rw [Expr.lowerLooseBVars'] <;> split <;> simp_all [FVarsIn]

theorem GhostFree.instantiateLevelParams (h : GhostFree G e) (hl : ∀ l ∈ ls, l.hasMVar' = false) :
    GhostFree G (e.instantiateLevelParams ps ls) := FVarsIn.instantiateLevelParams h hl

theorem GhostFree.sort_iff : GhostFree G (.sort l) ↔ l.hasMVar' = false := Iff.rfl

theorem GhostFree.sortLevel! : ∀ {e : Expr}, GhostFree G e → e.sortLevel!.hasMVar' = false
  | .sort .., h => h
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .app .., _ | .const .., _
  | .lam .., _ | .forallE .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simp [Expr.sortLevel!]; rfl

/-! ### `cheapBetaReduce` -/

theorem GhostFree.cheapBetaReduce (h : GhostFree G e) : GhostFree G e.cheapBetaReduce := by
  simp only [Expr.cheapBetaReduce, Id.run]
  split; · exact h
  split; · exact h
  have hargs := h.getAppArgs
  have hcont : ∀ i fn, GhostFree G fn → GhostFree G (Expr.cheapBetaReduce.cont e e.getAppArgs i fn) := by
    intro i fn hfn
    unfold Expr.cheapBetaReduce.cont
    split
    · exact hfn.mkAppRange hargs
    split
    · split
      · exact (hargs.getElem! _).mkAppRange hargs
      · exact GhostFree.panic
    · exact h
  have hloop : ∀ i fn, GhostFree G fn → GhostFree G (Expr.cheapBetaReduce.loop e e.getAppArgs i fn) := by
    intro i fn hfn
    induction fn generalizing i with
    | lam _ _ body _ _ ih =>
      unfold Expr.cheapBetaReduce.loop; split
      · exact ih _ hfn.2
      · exact hcont _ _ hfn
    | _ => unfold Expr.cheapBetaReduce.loop; split <;> exact hcont _ _ hfn
  exact hloop _ _ h.getAppFn

/-! ### Binding over the checker's own free variables -/

/-- Every element of the array is a free variable that is not a ghost. -/
def NonGhostFVars (G : FVarId → Prop) (arr : Array Expr) : Prop := ∀ x ∈ arr, ∃ id, x = .fvar id ∧ ¬ G id

theorem NonGhostFVars.empty : NonGhostFVars G #[] := nofun

theorem NonGhostFVars.push {arr : Array Expr} {id : FVarId} (h : NonGhostFVars G arr) (hid : ¬ G id) :
    NonGhostFVars G (arr.push (.fvar id)) := by
  intro x hx; rcases Array.mem_push.1 hx with hx | rfl
  · exact h _ hx
  · exact ⟨_, rfl, hid⟩

theorem NonGhostFVars.gfArr {arr : Array Expr} (h : NonGhostFVars G arr) : GhostFreeArr G arr := by
  intro x hx; obtain ⟨id, rfl, hid⟩ := h x hx; exact hid

theorem NonGhostFVars.eq_map {arr : Array Expr} (h : NonGhostFVars G arr) :
    ∃ xs : List FVarId, arr = ⟨xs.map .fvar⟩ ∧ ∀ x ∈ xs, ¬ G x := by
  obtain ⟨l⟩ := arr
  induction l with
  | nil => exact ⟨[], rfl, nofun⟩
  | cons a l ih =>
    obtain ⟨id, rfl, hid⟩ := h a (by simp)
    obtain ⟨xs, eq, hxs⟩ := ih fun x hx => h x (by simp at hx ⊢; exact .inr hx)
    cases eq
    exact ⟨id :: xs, rfl, by simp; exact ⟨hid, hxs⟩⟩

/-- The declarations of a local context at the given variables are ghost-free. -/
def DeclsGhostFree (G : FVarId → Prop) (lctx : LocalContext) (xs : List FVarId) : Prop :=
  ∀ x ∈ xs, ∀ ⦃d⦄, lctx.find? x = some d → GhostFree G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GhostFree G v

-- Used by `Lean4Lean/Verify/TypeChecker/FrameWHNF.lean`.
alias value?_ldecl := LocalDecl.value?_ldecl_true

theorem GhostFree.mkBindingList1N (hb : GhostFree G b)
    (hd : ∀ ⦃d⦄, lctx.find? x = some d → GhostFree G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GhostFree G v) :
    GhostFree G (LocalContext.mkBindingList1N isLambda lctx ys x b) := by
  unfold LocalContext.mkBindingList1N
  split
  · rename_i h; have := (hd h).1
    split
    · exact ⟨GhostFree.abstractN this, hb⟩
    · exact ⟨GhostFree.abstractN this, hb⟩
  · rename_i h; have := hd h
    split
    · exact ⟨GhostFree.abstractN this.1, GhostFree.abstractN (this.2 LocalDecl.value?_ldecl_true), hb⟩
    · exact hb.lowerLooseBVars'
  · exact GhostFree.panic

theorem GhostFree.mkBindingListN (hb : GhostFree G b) (hd : DeclsGhostFree G lctx xs) :
    GhostFree G (LocalContext.mkBindingListN isLambda lctx xs b) := by
  unfold LocalContext.mkBindingListN LocalContext.mkBindingListN.core
  have : ∀ ys : List FVarId, (∀ x ∈ ys, x ∈ xs) → ∀ b : Expr, GhostFree G b →
      GhostFree G (LocalContext.mkBindingListN.go isLambda lctx ys b) := by
    intro ys; induction ys with
    | nil => intro _ b hb; exact hb
    | cons y ys ih =>
      intro hys b hb
      simp only [LocalContext.mkBindingListN.go]
      exact ih (fun x hx => hys x (.tail _ hx)) _
        (GhostFree.mkBindingList1N hb (hd y (hys y (.head _))))
  exact this _ (fun x hx => List.mem_reverse.1 hx) _ hb.abstractN

theorem GhostRel.mkBinding {c₁ c₂ : Context} (hr : GhostRel G c₁ c₂) {arr : Array Expr}
    (hfv : NonGhostFVars G arr) (hb : GhostFree G b) :
    c₁.lctx.mkBinding isLambda arr b = c₂.lctx.mkBinding isLambda arr b ∧
    GhostFree G (c₂.lctx.mkBinding isLambda arr b) := by
  obtain ⟨xs, rfl, hxs⟩ := hfv.eq_map
  rw [LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN]
  exact ⟨LocalContext.mkBindingListN_congr_setIndex fun x hx => hr.find? (hxs x hx),
    GhostFree.mkBindingListN hb fun x _ _ hd => hr.decls hd⟩

theorem M.PreservesGhostRestriction.getLCtx_mkBinding {arr : Array Expr} (hfv : NonGhostFVars G arr) (hb : GhostFree G b) :
    M.PreservesGhostRestriction G (getLCtx >>= fun l => Pure.pure (l.mkBinding isLambda arr b)) (GhostFree G) := by
  intro c₁ c₂ s a s' hr hs e
  have := hr.mkBinding (isLambda := isLambda) hfv hb
  change Except.ok (c₁.lctx.mkBinding isLambda arr b, s) = _ at e
  rw [this.1] at e; cases e
  exact ⟨rfl, this.2, hs, .rfl⟩

theorem RecM.PreservesGhostRestriction.getLCtx_mkForall {arr : Array Expr} (hfv : NonGhostFVars G arr) (hb : GhostFree G b) :
    RecM.PreservesGhostRestriction G (getLCtx >>= fun l => Pure.pure (l.mkForall arr b)) (GhostFree G) :=
  fun _ _ => M.PreservesGhostRestriction.getLCtx_mkBinding (isLambda := false) hfv hb

end Lean4Lean.TypeChecker
