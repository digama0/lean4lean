import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Typing.Telescope

/-! Inductive-checker adapters for forall and lambda telescopes.

Generic syntax comes from `Verify.Expr.Telescope`; anonymous-context translation,
residual typing and context conversion come from `Verify.Typing.Telescope`.
This module closes the header checking scopes (`SourceTelescope`, `ScopeEmbedding`,
`FrontScopeEmbedding`) and the recursor parameter suffix into those typed
certificates. It retains the phase-specific opening, positivity, local-context
array and binding-context lemmas used by the recursor construction. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

attribute [simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj
theorem Expr.abstractN_bvar_lt (fvs : List FVarId) (_h : n < k) :
    (Expr.bvar n).abstractN fvs k = .bvar n := rfl

@[simp] theorem Expr.abstractN_app :
    (Expr.app fn arg).abstractN fvs k = .app (fn.abstractN fvs k) (arg.abstractN fvs k) := rfl

theorem Expr.abstractN_mkAppN :
    (mkAppN fn args).abstractN fvs k =
      mkAppN (fn.abstractN fvs k) (args.map fun arg => arg.abstractN fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Expr.abstractN]

theorem Expr.abstractN_fvar_of_not_mem (hmem : fv ∉ fvs) :
    (Expr.fvar fv).abstractN fvs k = .fvar fv := by
  simp [Expr.abstractN, Expr.lastRevIdx?_eq_none_of_not_mem hmem]

/-- An expression without free variables is unchanged by abstraction. -/
theorem FVarsIn.abstractN_eq_self {e : Expr} (h : FVarsIn (fun _ => False) e)
    (xs : List FVarId) (k : Nat) : e.abstractN xs k = e := by
  induction e generalizing k with
  | fvar v => exact absurd h id
  | bvar | const | sort | mvar | lit => rfl
  | mdata _ e ih | proj _ _ e ih => simp [Expr.abstractN, ih h]
  | app f a ihf iha => simp [Expr.abstractN, ihf h.1, iha h.2]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb => simp [Expr.abstractN, iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb => simp [Expr.abstractN, iht h.1, ihv h.2.1, ihb h.2.2]

theorem Expr.abstractList_mkAppN :
    (mkAppN fn args).abstractList fvs k =
      mkAppN (fn.abstractList fvs k)
        (args.map fun arg => arg.abstractList fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

theorem Expr.mkAppRange_to_end
    (fn : Expr) (args : Array Expr) (start : Nat)
    (hstart : start ≤ args.size) :
    mkAppRange fn start args.size args =
      Expr.mkAppList fn (args.toList.drop start) := by
  apply Expr.mkAppRange_eq
      (l₁ := args.toList.take start) (l₂ := args.toList.drop start)
      (l₃ := [])
  · simp
  · simp [List.length_take, Nat.min_eq_left hstart]
  · simp

theorem Expr.mkAppRange_from_zero
    (fn : Expr) (args : Array Expr) (stop : Nat)
    (hstop : stop ≤ args.size) :
    mkAppRange fn 0 stop args =
      Expr.mkAppList fn (args.toList.take stop) := by
  apply Expr.mkAppRange_eq
      (l₁ := []) (l₂ := args.toList.take stop)
      (l₃ := args.toList.drop stop)
  · simp
  · rfl
  · simp [List.length_take, Nat.min_eq_left hstop]

theorem Expr.getAppArgsList_mkAppList_const
    (name : Name) (levels : List Level) (args : List Expr) :
    (Expr.mkAppList (.const name levels) args).getAppArgsList = args := by
  rw [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_const]
  simp

/-- Abstraction at an inner cutoff preserves every already-valid outer bound
variable and adds one new valid slot. -/
theorem Closed.abstract1_at
    (H : Closed e (depth + outer)) :
    Closed (Expr.abstract1 fv e depth) (depth + outer + 1) := by
  induction e generalizing depth outer <;>
    simp_all [Closed, Expr.abstract1, Nat.add_assoc]
  case bvar i =>
    split <;> omega
  case fvar =>
    split <;> simp [Closed]
  case lam body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  case forallE body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  case letE body_ih =>
    have Hbody := body_ih (depth := depth + 1) (outer := outer) (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H.2.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody

/-- List abstraction at an inner cutoff preserves an existing outer de
Bruijn prefix and extends it by exactly the number of selected variables. -/
theorem Closed.abstractList_at
    (H : Closed e (depth + outer)) :
    Closed (e.abstractList fvars depth)
      (depth + outer + fvars.length) := by
  induction fvars generalizing e outer with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList, List.length_cons]
    have Hhead := Closed.abstract1_at (fv := fv) H
    have Htail := ih (outer := outer + 1) Hhead
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Htail

theorem _root_.Lean4Lean.Closed.mkAppList_iff {fn : Expr} {args : List Expr}
    {k : Nat} :
    Closed (Expr.mkAppList fn args) k ↔
      Closed fn k ∧ ∀ a ∈ args, Closed a k := by
  induction args generalizing fn with
  | nil => simp [Expr.mkAppList]
  | cons a as ih =>
    simp only [Expr.mkAppList, ih, Closed, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩

theorem _root_.Lean4Lean.Closed.getAppArgsList_at {e : Expr} {k : Nat}
    (h : Closed e k) {a : Expr} (ha : a ∈ e.getAppArgsList) : Closed a k := by
  have h' : Closed (Expr.mkAppList e.getAppFn e.getAppArgsList) k := by
    rwa [Expr.mkAppList_getAppArgsList]
  exact (Closed.mkAppList_iff.mp h').2 a ha

/-- Abstracting free variables below `extra` freshly introduced binders is
the same operation as abstracting at the original depth and weakening the
result.  Closedness rules out pre-existing loose variables at the insertion
cut, so the two de Bruijn presentations agree exactly. -/
theorem Expr.abstractList_add_eq_liftLooseBVars
    (Hclosed : Closed e depth) (Hnodup : fvars.Nodup) :
    e.abstractList fvars (depth + extra) =
      (e.abstractList fvars depth).liftLooseBVars' depth extra := by
  induction e generalizing depth extra with
  | bvar i =>
    simp only [Closed] at Hclosed
    rw [Expr.abstractList_bvar_lt fvars (by omega),
      Expr.abstractList_bvar_lt fvars Hclosed]
    simp [Expr.liftLooseBVars', Hclosed]
  | fvar fv =>
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    rcases Hclosed with ⟨Hfn, Harg⟩
    simp [Expr.liftLooseBVars', ihFn Hfn, ihArg Harg]
  | lam name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_lam, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | forallE name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_forallE, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    simp only [Expr.abstractList_letE, Expr.liftLooseBVars']
    rw [ihTy Hty, ihValue Hvalue]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed

/-- Weakening below an abstraction cutoff commutes with closing free
variables, provided the abstraction is moved past the inserted binders. -/
theorem Expr.liftLooseBVars'_abstractList_add
    (e : Expr) (fvars : List FVarId) (start cutoff amount : Nat)
    (Hcutoff : start ≤ cutoff) (Hnodup : fvars.Nodup) :
    (e.liftLooseBVars' start amount).abstractList fvars (cutoff + amount) =
      (e.abstractList fvars cutoff).liftLooseBVars' start amount := by
  induction e generalizing start cutoff amount with
  | bvar i =>
    by_cases hstart : i < start
    · rw [show (Expr.bvar i).liftLooseBVars' start amount = .bvar i by
          simp [Expr.liftLooseBVars', hstart],
        Expr.abstractList_bvar_lt fvars (by omega),
        Expr.abstractList_bvar_lt fvars (by omega)]
      simp [Expr.liftLooseBVars', hstart]
    · by_cases hcut : i < cutoff
      · rw [show (Expr.bvar i).liftLooseBVars' start amount =
              .bvar (i + amount) by
            simp [Expr.liftLooseBVars', hstart],
          Expr.abstractList_bvar_lt fvars (by omega),
          Expr.abstractList_bvar_lt fvars hcut]
        simp [Expr.liftLooseBVars', hstart]
      · obtain ⟨n, rfl⟩ : ∃ n, i = cutoff + n :=
          ⟨i - cutoff, by omega⟩
        have hge : ¬ cutoff + n < start := by omega
        have hgeAbstract :
            ¬ cutoff + n + fvars.length < start := by omega
        rw [show (Expr.bvar (cutoff + n)).liftLooseBVars' start amount =
              .bvar ((cutoff + amount) + n) by
            simp [Expr.liftLooseBVars', hge]; omega,
          Expr.abstractList_bvar_ge,
          Expr.abstractList_bvar_ge]
        simp [Expr.liftLooseBVars', hgeAbstract]
        omega
  | fvar fv =>
    simp only [Expr.liftLooseBVars']
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      congr 1
      omega
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    simp [Expr.liftLooseBVars', ihFn start cutoff amount Hcutoff,
      ihArg start cutoff amount Hcutoff]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_lam]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_forallE]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_letE]
    rw [ihTy start cutoff amount Hcutoff,
      ihValue start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff

/-- If closing a list of free variables yields a term scoped by exactly the
new de Bruijn prefix, the original term had no loose variables at the
abstraction cut. -/
theorem Expr.closed_of_abstractList
    (Hclosed : Closed (e.abstractList fvars depth)
      (depth + fvars.length)) :
    Closed e depth := by
  induction e generalizing depth with
  | bvar i =>
    by_cases hi : i < depth
    · exact hi
    · have heq : i = depth + (i - depth) := by omega
      rw [heq, Expr.abstractList_bvar_ge] at Hclosed
      simpa only [Closed] using (show i < depth from by
        simp only [Closed] at Hclosed
        omega)
  | fvar => trivial
  | sort => trivial
  | const => trivial
  | mvar id =>
    have heq : (Expr.mvar id).abstractList fvars depth =
        .mvar id := by
      clear Hclosed
      induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
    rw [heq] at Hclosed
    exact Hclosed
  | lit => trivial
  | app fn arg ihFn ihArg =>
    rw [Expr.abstractList_app] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hfn, Harg⟩
    exact ⟨ihFn Hfn, ihArg Harg⟩
  | lam name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_lam] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | forallE name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_forallE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rw [Expr.abstractList_letE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    refine ⟨ihTy Hty, ihValue Hvalue, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | mdata md body ih =>
    rw [Expr.abstractList_mdata] at Hclosed
    simpa only [Closed] using ih Hclosed
  | proj name idx body ih =>
    rw [Expr.abstractList_proj] at Hclosed
    simpa only [Closed] using ih Hclosed

theorem Expr.abstractN_fvar_getElem
    (hnd : fvs.Nodup) (i : Nat) (hi : i < fvs.length) :
    (Expr.fvar fvs[i]).abstractN fvs k = .bvar (k + (fvs.length - 1 - i)) := by
  rw [Expr.abstractN_eq_abstractList hnd _ _ (by simp [Expr.looseBVarRange'])]
  exact Expr.abstractList_fvar_getElem hnd i hi

theorem Expr.abstractN_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractN fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < fvs.length := by simpa using h1
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractN_fvar_getElem hnd i hi

theorem Expr.abstractList_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractList fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i (by simpa using hiLeft)

/-- Close an expression over one free-variable parameter array and reopen it
with another. -/
def Expr.reopenParams (e : Expr) (params restoreAs : Array Expr) : Expr :=
  (e.abstract params).instantiateRev restoreAs

/-- Transparent list model of parameter reopening at an arbitrary de Bruijn
depth. -/
def Expr.reopenFVarsAt (e : Expr) (fvars restoreFvars : List FVarId)
    (k : Nat := 0) : Expr :=
  (e.abstractList fvars k).instantiateRevList
    (restoreFvars.map Expr.fvar) k

theorem _root_.Lean4Lean.FVarsIn.abstractList_eq_self
    (H : e.FVarsIn fun fv => fv ∉ fvars) (Hclosed : Closed e k) :
    e.abstractList fvars k = e := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    simp only [List.mem_cons, not_or] at H
    simp only [Expr.abstractList]
    rw [(H.mono fun other hother => hother.1).abstract_eq_self Hclosed]
    exact ih (H.mono fun other hother => hother.2)

theorem Expr.reopenFVarsAt_eq_self_of_abstract
    (Habstract : ∀ k, e.abstractList fvars k = e)
    (Hrange : e.looseBVarRange' = 0) (k : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  unfold Expr.reopenFVarsAt
  rw [Habstract]
  exact Expr.instantiateRevList'_eq_self (by omega)

theorem Expr.abstractList_eq_self_of_abstract1
    (e : Expr) (H : ∀ fv k, e.abstract1 fv k = e)
    (fvars : List FVarId) (k : Nat) :
    e.abstractList fvars k = e := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih => simp [Expr.abstractList, H, ih]

theorem Expr.reopenFVarsAt_of_abstract1_eq_self
    (H : ∀ fv depth, e.abstract1 fv depth = e)
    (Hrange : e.looseBVarRange' = 0) (fvars restoreFvars : List FVarId)
    (k : Nat) : Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  apply Expr.reopenFVarsAt_eq_self_of_abstract
    (fun depth => Expr.abstractList_eq_self_of_abstract1 e H fvars depth)
    Hrange

theorem Expr.reopenFVarsAt_bvar
    (hsize : restoreFvars.length = fvars.length) (i k : Nat) :
    Expr.reopenFVarsAt (.bvar i) fvars restoreFvars k = .bvar i := by
  unfold Expr.reopenFVarsAt
  by_cases hi : i < k
  · rw [Expr.abstractList_bvar_lt fvars hi]
    exact Expr.instantiateRevList_bvar_fvars_lt restoreFvars i k hi
  · obtain ⟨n, rfl⟩ : ∃ n, i = k + n := by
      exact ⟨i - k, by omega⟩
    rw [Expr.abstractList_bvar_ge]
    rw [← hsize]
    exact Expr.instantiateRevList_bvar_fvars_ge restoreFvars k n

theorem Expr.reopenFVarsAt_selected
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (i : Nat) (hi : i < fvars.length) (k : Nat) :
    Expr.reopenFVarsAt (.fvar fvars[i]) fvars restoreFvars k =
      .fvar restoreFvars[i] := by
  unfold Expr.reopenFVarsAt
  rw [Expr.abstractList_fvar_getElem hnd i hi]
  rw [← hsize]
  exact Expr.instantiateRevList_bvar_fvars_getElem restoreFvars i k
    (by omega)

theorem Expr.reopenFVarsAt_fvar_exists
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (fv : FVarId) (k : Nat) :
    ∃ restored, Expr.reopenFVarsAt (.fvar fv) fvars restoreFvars k =
      .fvar restored := by
  by_cases hfv : fv ∈ fvars
  · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
    exact ⟨restoreFvars[i], Expr.reopenFVarsAt_selected hnd hsize i hi k⟩
  · refine ⟨fv, Expr.reopenFVarsAt_eq_self_of_abstract
      (fun depth => Expr.abstractList_fvar_of_not_mem hfv)
      (by simp [Expr.looseBVarRange']) k⟩

/-- Close-and-reopen free-variable renaming is independent of the de Bruijn
depth at which the surrounding syntax traversal encounters the expression. -/
theorem Expr.reopenFVarsAt_depth_independent
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k₁ k₂ : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k₁ =
      Expr.reopenFVarsAt e fvars restoreFvars k₂ := by
  induction e generalizing k₁ k₂ with
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize,
      Expr.reopenFVarsAt_bvar hsize]
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi,
        Expr.reopenFVarsAt_selected hnd hsize i hi]
    · have habstract : ∀ k, (Expr.fvar fv).abstractList fvars k = .fvar fv := by
        intro k
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₁,
        Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₂]
  | mvar id =>
    have habstract : ∀ k, (Expr.mvar id).abstractList fvars k = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.mvar id) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | sort u =>
    have habstract : ∀ k, (Expr.sort u).abstractList fvars k = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.sort u) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | const name levels =>
    have habstract : ∀ k, (Expr.const name levels).abstractList fvars k =
        .const name levels := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.const name levels) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | lit literal =>
    have habstract : ∀ k, (Expr.lit literal).abstractList fvars k =
        .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.lit literal) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app]
    change Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₁)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₁) =
      Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₂)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₂)
    rw [ihFn k₁ k₂, ihArg k₁ k₂]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam]
    change Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE]
    change Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE]
    change Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₁)
        (Expr.reopenFVarsAt value fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) nondep =
      Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₂)
        (Expr.reopenFVarsAt value fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) nondep
    rw [ihTy k₁ k₂, ihValue k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | mdata md body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata]
    change Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]
  | proj name idx body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj]
    change Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]

/-- Constant application heads are likewise reflected by free-variable
reopening. -/
theorem Expr.getAppFn_reopenFVarsAt_eq_const
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k : Nat)
    (H : (Expr.reopenFVarsAt e fvars restoreFvars k).getAppFn =
      .const name levels) :
    e.getAppFn = .const name levels := by
  induction e generalizing k with
  | app fn arg ihFn ihArg =>
    apply ihFn
    simpa [Expr.reopenFVarsAt, Expr.getAppFn] using H
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize] at H
    exact H
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi] at H
      cases H
    · have habstract : ∀ depth,
          (Expr.fvar fv).abstractList fvars depth = .fvar fv := by
        intro depth
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange'])] at H
      exact H
  | mvar id =>
    have habstract : ∀ depth,
        (Expr.mvar id).abstractList fvars depth = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1 (.mvar id)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | sort u =>
    have habstract : ∀ depth,
        (Expr.sort u).abstractList fvars depth = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1 (.sort u)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | const sourceName sourceLevels =>
    have habstract : ∀ depth,
        (Expr.const sourceName sourceLevels).abstractList fvars depth =
          .const sourceName sourceLevels := by
      exact Expr.abstractList_eq_self_of_abstract1 (.const sourceName sourceLevels)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lit literal =>
    have habstract : ∀ depth,
        (Expr.lit literal).abstractList fvars depth = .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1 (.lit literal)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lam name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | forallE name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | mdata md body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | proj typeName idx body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H

/-- The implementation's array operation is the depth-zero instance of the
transparent free-variable reopening model, provided the expression has no
loose bound variables.  Without that premise the exact `Expr.abstract` leaves
loose bound variables in place while the sequential list model shifts them. -/
theorem Expr.reopenParams_eq_reopenFVarsAt
    (hnd : fvars.Nodup)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (hlb : e.looseBVarRange' = 0) :
    Expr.reopenParams e params restoreAs =
      Expr.reopenFVarsAt e fvars restoreFvars 0 := by
  subst params
  subst restoreAs
  simp only [Expr.reopenParams, Expr.reopenFVarsAt,
    Expr.abstract_eq_of_closed e fvars hnd hlb,
    Expr.instantiateRev_eq, Expr.instantiate_eq, Array.toList_reverse,
    Expr.instantiateList_reverse]

/-- Reopening at the depth of a syntax traversal agrees with the operational
depth-zero parameter reopening for expressions without loose bound
variables. -/
theorem Expr.reopenFVarsAt_eq_reopenParams
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (e : Expr) (k : Nat) (hlb : e.looseBVarRange' = 0) :
    Expr.reopenFVarsAt e fvars restoreFvars k =
      Expr.reopenParams e params restoreAs := by
  rw [Expr.reopenFVarsAt_depth_independent hnd hsize e k 0]
  exact (Expr.reopenParams_eq_reopenFVarsAt hnd hparams hrestore hlb).symm

theorem Expr.reopenFVarsAt_app (fvars restoreFvars : List FVarId) (k : Nat) :
    Expr.reopenFVarsAt (.app fn arg) fvars restoreFvars k =
      .app (Expr.reopenFVarsAt fn fvars restoreFvars k)
        (Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  simp [Expr.reopenFVarsAt]

theorem Expr.reopenFVarsAt_const (fvars restoreFvars : List FVarId) (k : Nat) :
    Expr.reopenFVarsAt (.const name levels) fvars restoreFvars k =
      .const name levels :=
  Expr.reopenFVarsAt_of_abstract1_eq_self
    (by intro fv depth; simp [Expr.abstract1])
    (by simp [Expr.looseBVarRange']) fvars restoreFvars k

theorem Expr.reopenFVarsAt_mkAppList (fvars restoreFvars : List FVarId)
    (k : Nat) :
    Expr.reopenFVarsAt (Expr.mkAppList fn args) fvars restoreFvars k =
      Expr.mkAppList (Expr.reopenFVarsAt fn fvars restoreFvars k)
        (args.map fun arg => Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.mkAppList, List.map_cons]
    rw [ih, Expr.reopenFVarsAt_app]

theorem Expr.reopenFVarsAt_of_getAppFn_const (fvars restoreFvars : List FVarId)
    (k : Nat) (hhead : input.getAppFn = .const name levels) :
    Expr.reopenFVarsAt input fvars restoreFvars k =
      Expr.mkAppList (.const name levels)
        (input.getAppArgsList.map fun arg =>
          Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  calc
    Expr.reopenFVarsAt input fvars restoreFvars k =
        Expr.reopenFVarsAt
          (Expr.mkAppList input.getAppFn input.getAppArgsList)
          fvars restoreFvars k :=
      congrArg (fun e => Expr.reopenFVarsAt e fvars restoreFvars k)
        (Expr.mkAppList_getAppArgsList input).symm
    _ = Expr.mkAppList
          (Expr.reopenFVarsAt input.getAppFn fvars restoreFvars k)
          (input.getAppArgsList.map fun arg =>
            Expr.reopenFVarsAt arg fvars restoreFvars k) :=
      Expr.reopenFVarsAt_mkAppList fvars restoreFvars k
    _ = _ := by
      rw [hhead, Expr.reopenFVarsAt_const]

theorem Expr.abstractList_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractList binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractList_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

theorem Expr.abstractN_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractN binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractN_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

/-- Closing one free variable does not change the head of an application
spine, except for closing that head itself. -/
theorem Expr.getAppFn_abstract1 (e : Expr) (fv : FVarId) (k : Nat := 0) :
    (e.abstract1 fv k).getAppFn = e.getAppFn.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simpa [Expr.abstract1, Expr.getAppFn] using ihFn k
  | bvar i => simp [Expr.abstract1, Expr.getAppFn]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppFn, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppFn]

/-- Closing free variables does not change the head of an application spine,
except for closing that head itself. -/
theorem Expr.getAppFn_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppFn =
      e.getAppFn.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    exact congrArg (fun head => head.abstractList fvars k)
      (Expr.getAppFn_abstract1 e fv k)

/-- Closing one free variable acts pointwise on the arguments of an
application spine and preserves their order. -/
theorem Expr.getAppArgsList_abstract1 (e : Expr) (fv : FVarId)
    (k : Nat := 0) :
    (e.abstract1 fv k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simp only [Expr.abstract1, Expr.getAppArgsList_app, ihFn,
      List.map_append, List.map_cons, List.map_nil]
  | bvar i => simp [Expr.abstract1, Expr.getAppArgsList]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppArgsList, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppArgsList]

/-- Closing free variables acts pointwise on the arguments of an application
spine and preserves their order. -/
theorem Expr.getAppArgsList_abstractList (e : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => simp
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    calc
      ((e.abstract1 fv k).abstractList fvars k).getAppArgsList =
          (e.abstract1 fv k).getAppArgsList.map
            (fun arg => arg.abstractList fvars k) := ih _
      _ = (e.getAppArgsList.map fun arg => arg.abstract1 fv k).map
            (fun arg => arg.abstractList fvars k) :=
        congrArg (fun args => args.map
          (fun arg => arg.abstractList fvars k))
          (Expr.getAppArgsList_abstract1 e fv k)
      _ = e.getAppArgsList.map fun arg =>
          (arg.abstract1 fv k).abstractList fvars k := by
        simp only [List.map_map]
        apply congrArg (fun f => List.map f e.getAppArgsList)
        funext arg
        rfl

/-- Array form of `getAppArgsList_abstractList`. -/
theorem Expr.getAppArgs_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgs =
      e.getAppArgs.map fun arg => arg.abstractList fvars k := by
  apply Array.toList_inj.mp
  simp only [Expr.getAppArgs_toList, Expr.getAppArgsList_abstractList,
    Array.toList_map]

/-- Closing free variables acts pointwise on the index suffix returned by
`getIIndices`; the classifier component is irrelevant to this projection. -/
theorem checkPositivityStep.getIIndices.snd_abstractList
    (stats : AddInductive.InductiveStats) (type : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    (AddInductive.getIIndices stats (type.abstractList fvars k)).2 =
      (AddInductive.getIIndices stats type).2.map
        (fun index => index.abstractList fvars k) := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map]
  have suffixToList (e : Expr) :
      (AddInductive.getIIndices stats e).2.toList =
        e.getAppArgs.toList.drop stats.params.size := by
    simp only [AddInductive.getIIndices]
    let suffix := e.getAppArgs.toSubarray stats.params.size
    calc
      (Std.Slice.toArray suffix).toList = suffix.toList := by
        exact (congrArg Array.toList
          (Subarray.toArray_eq_sliceToArray (s := suffix)).symm).trans
            Subarray.toList_toArray
      _ = e.getAppArgs.toList.drop stats.params.size := by
        rw [List.drop_eq_drop_min]
        simp only [suffix, Subarray.toList_eq, Array.array_toSubarray,
          Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
          Array.toList_extract, List.extract_eq_take_drop,
          Array.length_toList]
        apply List.take_of_length_le
        simp
  rw [suffixToList, suffixToList]
  simp [Expr.getAppArgs_toList, Expr.getAppArgsList_abstractList]

/-- The concrete inductive-occurrence scan observes only constants, so
closing a free variable cannot affect its result. -/
theorem checkPositivityStep.hasIndOcc_abstract1
    (indConsts : Array Expr) (e : Expr) (fv : FVarId) (k : Nat := 0) :
    AddInductive.hasIndOcc indConsts (e.abstract1 fv k) =
      AddInductive.hasIndOcc indConsts e := by
  rw [checkPositivityStep.hasIndOcc_eq_findAny,
    checkPositivityStep.hasIndOcc_eq_findAny]
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1, Expr.findAny]
  | fvar other =>
    by_cases h : fv == other
    · simp [Expr.abstract1, Expr.findAny, h]
    · simp [Expr.abstract1, Expr.findAny, h]
  | mvar | sort | const | lit => simp [Expr.abstract1, Expr.findAny]
  | app fn arg ihFn ihArg =>
    simp [Expr.abstract1, Expr.findAny, ihFn, ihArg]
  | lam name dom body bi ihDom ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihDom, ihBody]
  | forallE name dom body bi ihDom ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihDom, ihBody]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp [Expr.abstract1, Expr.findAny, ihTy, ihValue, ihBody]
  | mdata md body ih => simp [Expr.abstract1, Expr.findAny, ih]
  | proj name idx body ih => simp [Expr.abstract1, Expr.findAny, ih]

/-- Simultaneously closing any list of free variables preserves the concrete
inductive-occurrence scan. -/
theorem checkPositivityStep.hasIndOcc_abstractList
    (indConsts : Array Expr) (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    AddInductive.hasIndOcc indConsts (e.abstractList fvars k) =
      AddInductive.hasIndOcc indConsts e := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    exact checkPositivityStep.hasIndOcc_abstract1 indConsts e fv k

/-- Closing a free variable cannot manufacture a constant. -/
theorem Expr.abstract1_eq_const
    {e : Expr} {fv : FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstract1 fv k = .const name levels) :
    e = .const name levels := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true <;> simp [Expr.abstract1, h] at H
  | mvar | sort | lit => simp [Expr.abstract1] at H
  | const => simpa [Expr.abstract1] using H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Iterated closing likewise reflects constant syntax. -/
theorem Expr.abstractList_eq_const
    {e : Expr} {fvars : List FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstractList fvars k = .const name levels) :
    e = .const name levels := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [Expr.abstractList] at H
    exact Expr.abstract1_eq_const (ih H)

/-- A resulting free variable was already that exact free variable in the source. -/
theorem Expr.abstract1_eq_fvar
    {e : Expr} {target fv : FVarId} {k : Nat}
    (H : e.abstract1 fv k = .fvar target) :
    e = .fvar target := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true
    · simp [Expr.abstract1, h] at H
    · simp only [Expr.abstract1, h] at H
      cases H
      rfl
  | mvar | sort | const | lit => simp [Expr.abstract1] at H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Reflection of a free variable through a list abstraction. -/
theorem Expr.abstractList_eq_fvar
    {e : Expr} {target : FVarId} {fvars : List FVarId} {k : Nat}
    (H : e.abstractList fvars k = .fvar target) :
    e = .fvar target := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [Expr.abstractList] at H
    have Hinter : e.abstract1 fv k = .fvar target := ih H
    exact Expr.abstract1_eq_fvar (target := target) (fv := fv)
      Hinter

/-- A valid concrete inductive application remains valid after closing a
set of fresh field variables.  The disjointness premise says precisely that
the cached common parameters belong to the older root context. -/
theorem checkPositivityStep.isValidIndAppIdx.abstractList
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (paramFvars binders : List FVarId)
    (hparams : stats.params = (paramFvars.map Expr.fvar).toArray)
    (hdisjoint : ∀ fv, fv ∈ paramFvars → fv ∉ binders)
    (k : Nat := 0) :
    AddInductive.isValidIndAppIdx stats
      (type.abstractList binders k) i = true := by
  have hconstGet : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalid hconst
  have habstractHead : (type.abstractList binders k).getAppFn =
      .const name levels := by
    rw [Expr.getAppFn_abstractList type binders k, hhead]
    induction binders <;> simp_all [Expr.abstractList, Expr.abstract1]
  have hheadClosed :
      ((type.abstractList binders k).getAppFn == stats.indConsts[i]!) =
        true := by
    simpa only [habstractHead, hconstGet] using
      (beq_self_eq_true (Expr.const name levels))
  have harityClosed : (type.abstractList binders k).getAppArgs.size =
      stats.params.size + stats.nindices[i]! := by
    rw [Expr.getAppArgs_abstractList type binders k, Array.size_map]
    exact checkPositivityStep.isValidIndAppIdx.arity hvalid
  have hparamsClosed : ∀ j
      (hj : j < stats.params.size),
      stats.params[j] =
        (type.abstractList binders k).getAppArgs[j]'(by omega) := by
    intro j hj
    have hsize : stats.params.size = paramFvars.length := by
      rw [hparams]
      simp
    have hjFvars : j < paramFvars.length := by omega
    have hjSource : j < type.getAppArgs.size := by
      have := checkPositivityStep.isValidIndAppIdx.arity hvalid
      omega
    have hjClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      omega
    have hparamAt : stats.params[j] = .fvar paramFvars[j] := by
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hparams
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjFvars] using hget
    have hargEqv := checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hparamAt] at hargEqv
    have harg : type.getAppArgs[j]'hjSource = .fvar paramFvars[j] :=
      Expr.eqv_fvar_eq hargEqv
    have habstractArg :
        (type.abstractList binders k).getAppArgs[j]'hjClosed =
          .fvar paramFvars[j] := by
      have hargs := Expr.getAppArgs_abstractList type binders k
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
      have habstract :
          (type.getAppArgs[j]'hjSource).abstractList binders k =
            .fvar paramFvars[j] := by
        rw [harg]
        exact Expr.abstractList_fvar_of_not_mem
          (hdisjoint paramFvars[j] (List.getElem_mem hjFvars))
      simpa [Array.getElem!_eq_getD, Array.getD, hjClosed, hjSource,
        habstract] using hget
    exact hparamAt.trans habstractArg.symm
  have hindicesClosed : ∀ j
      (hlower : stats.params.size ≤ j)
      (hupper : j < (type.abstractList binders k).getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts
        (type.abstractList binders k).getAppArgs[j] = false := by
    intro j hlower hupper
    have hupperSource : j < type.getAppArgs.size := by
      simpa only [Expr.getAppArgs_abstractList type binders k,
        Array.size_map] using hupper
    have hsource :=
      checkPositivityStep.isValidIndAppIdx.indexNoOccurrence hvalid
        hlower hupperSource
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have hargEq :
        (type.abstractList binders k).getAppArgs[j]'hupper =
          (type.getAppArgs[j]'hupperSource).abstractList binders k := by
      simpa [Array.getElem!_eq_getD, Array.getD, hupper,
        hupperSource] using hget
    calc
      AddInductive.hasIndOcc stats.indConsts
          (type.abstractList binders k).getAppArgs[j] =
          AddInductive.hasIndOcc stats.indConsts
            ((type.getAppArgs[j]'hupperSource).abstractList binders k) :=
        congrArg (AddInductive.hasIndOcc stats.indConsts) hargEq
      _ = AddInductive.hasIndOcc stats.indConsts
          type.getAppArgs[j] :=
        checkPositivityStep.hasIndOcc_abstractList stats.indConsts
          type.getAppArgs[j] binders k
      _ = false := hsource
  exact checkPositivityStep.isValidIndAppIdx.intro hheadClosed harityClosed
    hparamsClosed hindicesClosed

/-- Conversely, closing fresh field variables cannot turn an invalid application into a
valid one. With `abstractList`, this shows that validity does not depend on the names of
the field variables, which differ between the constructor check and the recursor
construction. -/
theorem checkPositivityStep.isValidIndAppIdx.of_abstractList
    (paramFvars binders : List FVarId) (k : Nat := 0)
    (hvalid : AddInductive.isValidIndAppIdx stats
      (type.abstractList binders k) i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels))
    (hparams : stats.params = (paramFvars.map Expr.fvar).toArray) :
    AddInductive.isValidIndAppIdx stats type i = true := by
  have hconstGet : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  have habstractHead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalid hconst
  have habstractSourceHead :
      type.getAppFn.abstractList binders k = .const name levels := by
    rw [← Expr.getAppFn_abstractList type binders k]
    exact habstractHead
  have hsourceHead : type.getAppFn = .const name levels :=
    Expr.abstractList_eq_const habstractSourceHead
  have hheadSource : (type.getAppFn == stats.indConsts[i]!) = true := by
    simpa only [hsourceHead, hconstGet] using
      (beq_self_eq_true (Expr.const name levels))
  have haritySource : type.getAppArgs.size =
      stats.params.size + stats.nindices[i]! := by
    have hclosed := checkPositivityStep.isValidIndAppIdx.arity hvalid
    simpa only [Expr.getAppArgs_abstractList type binders k,
      Array.size_map] using hclosed
  have hparamsSource : ∀ j (hj : j < stats.params.size),
      stats.params[j] = type.getAppArgs[j]'(by omega) := by
    intro j hj
    have hsize : stats.params.size = paramFvars.length := by
      rw [hparams]
      simp
    have hjFvars : j < paramFvars.length := by omega
    have hjSource : j < type.getAppArgs.size := by omega
    have hjClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      have := checkPositivityStep.isValidIndAppIdx.arity hvalid
      omega
    have hparamAt : stats.params[j] = .fvar paramFvars[j] := by
      have hget := congrArg (fun xs : Array Expr => xs[j]!) hparams
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjFvars] using hget
    have hclosedEqv :=
      checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hparamAt] at hclosedEqv
    have hclosedArg :
        (type.abstractList binders k).getAppArgs[j]'hjClosed =
          .fvar paramFvars[j] := Expr.eqv_fvar_eq hclosedEqv
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have habstractArg :
        (type.getAppArgs[j]'hjSource).abstractList binders k =
          .fvar paramFvars[j] := by
      have hpointwise :
          (type.abstractList binders k).getAppArgs[j]'hjClosed =
            (type.getAppArgs[j]'hjSource).abstractList binders k := by
        simpa [Array.getElem!_eq_getD, Array.getD, hjClosed,
          hjSource] using hget
      exact hpointwise.symm.trans hclosedArg
    have hsourceArg : type.getAppArgs[j]'hjSource =
        .fvar paramFvars[j] :=
      Expr.abstractList_eq_fvar habstractArg
    exact hparamAt.trans hsourceArg.symm
  have hindicesSource : ∀ j (hlower : stats.params.size ≤ j)
      (hupper : j < type.getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
    intro j hlower hupper
    have hupperClosed : j <
        (type.abstractList binders k).getAppArgs.size := by
      simpa only [Expr.getAppArgs_abstractList type binders k,
        Array.size_map] using hupper
    have hclosed :=
      checkPositivityStep.isValidIndAppIdx.indexNoOccurrence hvalid
        hlower hupperClosed
    have hargs := Expr.getAppArgs_abstractList type binders k
    have hget := congrArg (fun xs : Array Expr => xs[j]!) hargs
    have hargEq :
        (type.abstractList binders k).getAppArgs[j]'hupperClosed =
          (type.getAppArgs[j]'hupper).abstractList binders k := by
      simpa [Array.getElem!_eq_getD, Array.getD, hupperClosed,
        hupper] using hget
    calc
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] =
          AddInductive.hasIndOcc stats.indConsts
            ((type.getAppArgs[j]'hupper).abstractList binders k) :=
        (checkPositivityStep.hasIndOcc_abstractList stats.indConsts
          type.getAppArgs[j] binders k).symm
      _ = AddInductive.hasIndOcc stats.indConsts
          (type.abstractList binders k).getAppArgs[j] :=
        congrArg (AddInductive.hasIndOcc stats.indConsts) hargEq.symm
      _ = false := hclosed
  exact checkPositivityStep.isValidIndAppIdx.intro hheadSource haritySource
    hparamsSource hindicesSource

/-- Opening one more telescope binder and then closing the complete ordered
field list recovers the body obtained by stripping that binder from the
already-closed telescope. -/
theorem Expr.instantiate1_fvar_abstractList_append
    {fv : FVarId} {fvars : List FVarId} {body : Expr}
    (hfv : fv ∉ fvars)
    (hbody : body.FVarsIn (fun other => other ≠ fv)) :
    (body.instantiate1 (.fvar fv)).abstractList (fvars ++ [fv]) =
      body.abstractList fvars 1 := by
  rw [Expr.abstractList_append]
  simp only [Expr.abstractList]
  rw [Expr.abstract1_abstractList hfv]
  rw [Expr.instantiate1_eq, hbody.abstract_instantiate1]

/-- Closing free variables changes leaves but never the outer expression
constructor, so in particular it cannot create or remove a leading forall. -/
@[simp] theorem Expr.abstractList_isForall
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).isForall = e.isForall := by
  induction fvars generalizing e k with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    cases e <;> simp only [Expr.abstract1, Expr.isForall]
    case fvar fvarId =>
      by_cases h : (fv == fvarId) = true
      · rw [if_pos h]
      · rw [if_neg h]

/-- The opening of a constructor telescope by a field traversal. `current` is the opened
residual the executable sees, while `residual` is the same point of the source telescope
with all opened fields closed back to de Bruijn variables, which does not depend on the
names chosen for the fields. -/
structure ConstructorFieldOpening
    (source current : Expr) (fields : Array Expr) : Type where
  fvars : List FVarId
  expressions : fields = (fvars.map Expr.fvar).toArray
  nodup : fvars.Nodup
  residual : Expr
  telescope : Expr.ForallTelescope source fields.size residual
  closed : current.abstractList fvars = residual

def ConstructorFieldOpening.empty (source : Expr) :
    ConstructorFieldOpening source source #[] where
  fvars := []
  expressions := rfl
  nodup := .nil
  residual := source
  telescope := .nil source
  closed := rfl

/-- Extend the opening by the fresh field chosen by `withLocalDecl`. -/
def ConstructorFieldOpening.push
    (H : ConstructorFieldOpening source
      (.forallE name dom body bi) fields)
    (hfv : fv ∉ H.fvars)
    (hbody : body.FVarsIn (fun other => other ≠ fv)) :
    ConstructorFieldOpening source
      (body.instantiate1 (.fvar fv))
      (fields.push (.fvar fv)) := by
  have hsize : fields.size = H.fvars.length := by
    have := congrArg Array.size H.expressions
    simpa using this
  let nextResidual := body.abstractList H.fvars 1
  have Hinner : Expr.ForallTelescope H.residual 1 nextResidual := by
    rw [← H.closed]
    simp only [Expr.abstractList_forallE]
    exact .cons (.nil nextResidual)
  refine {
    fvars := H.fvars ++ [fv]
    expressions := ?_
    nodup := ?_
    residual := nextResidual
    telescope := ?_
    closed := ?_ }
  · simp [H.expressions]
  · apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro other hother selected hselected
    simp only [List.mem_singleton] at hselected
    subst selected
    exact fun heq => hfv (heq ▸ hother)
  · have Htel := H.telescope.trans Hinner
    simpa [hsize] using Htel
  · exact Expr.instantiate1_fvar_abstractList_append hfv hbody

theorem Expr.abstractN_indexBVars
    (binders : List FVarId) (n k : Nat) (_hk : n < k) :
    ((List.ofFn fun i : Fin n =>
        Expr.bvar (1 + (n - 1 - i))).toArray.map
      fun e => e.abstractN binders k) =
    (List.ofFn fun i : Fin n =>
      Expr.bvar (1 + (n - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_ofFn]
    rfl

/-- Close the front of a front scope embedding. The abstract target is unchanged; the
source is abstracted over the front's free variables in oldest-first order, and the
resulting anonymous telescope sits directly above the base scope. -/
theorem checkInductiveTypes.loopType.FrontScopeEmbedding.abstractFront
    (H : checkInductiveTypes.loopType.FrontScopeEmbedding
      env Us scope runtime)
    (henv : env.WF)
    (hbase : scope.drop H.frontSourceDomains.length = baseScope)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext H.frontSourceDomains baseScope)
      (source.abstractList
        (VLCtx.fvars (scope.take H.frontSourceDomains.length)).reverse)
      target := by
  let scopePrefix := scope.take H.frontSourceDomains.length
  let tail := scope.drop H.frontSourceDomains.length
  have hscope : scopePrefix ++ tail = scope := by
    simp [scopePrefix, tail]
  have Htr' : TrExprS env Us
      (abstractForallContext [] (scopePrefix ++ tail)) source target := by
    simpa [abstractForallContext, hscope] using Htr
  have hnodup : (VLCtx.fvars scopePrefix).Nodup := by
    exact (VLCtx.fvars_take_sublist scope
      H.frontSourceDomains.length).nodup (H.scopeWF henv).fvars_nodup
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    (domains := []) H.front.sourceDeclarations hnodup Htr'
  simpa [scopePrefix, tail, H.front.sourceTakenContext, hbase] using
    Habstract

/-- The free variables of a scope are those of its front followed by those of its
base. -/
theorem checkInductiveTypes.loopType.FrontScopeEmbedding.frontFVars
    (H : checkInductiveTypes.loopType.FrontScopeEmbedding
      env Us scope runtime)
    (hbase : scope.drop H.frontSourceDomains.length = baseScope) :
    scope.fvars =
      VLCtx.fvars (scope.take H.frontSourceDomains.length) ++
        VLCtx.fvars baseScope := by
  calc
    scope.fvars = VLCtx.fvars
        (scope.take H.frontSourceDomains.length ++
          scope.drop H.frontSourceDomains.length) := by
      rw [List.take_append_drop]
    _ = VLCtx.fvars (scope.take H.frontSourceDomains.length) ++
        VLCtx.fvars (scope.drop H.frontSourceDomains.length) := by
      rw [VLCtx.fvars_append]
    _ = _ := by rw [hbase]

/-- Close every declaration of a (not necessarily contiguous) scope embedding. The binder
order is `scope.fvars`, so the resulting anonymous telescope abstracts the source in
oldest-first order without assuming that the declarations form a prefix of the executable
context. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.abstractAll
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList scope.fvars.reverse) target := by
  have Htr' : TrExprS env Us
      (abstractForallContext [] scope) source target := by
    simpa [abstractForallContext] using Htr
  have hnodup : scope.fvars.Nodup :=
    (H.scopeWF henv).fvars_nodup
  simpa using TrExprS.abstractFVarLambdaSuffix
    H.declarations hnodup Htr'

/-- The anonymous telescope obtained by closing a scope embedding is well formed. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.abstractAllWF
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    OnCtx (abstractForallContext scope.toCtx.reverse []).toCtx
      (env.IsType Us.length) := by
  have Hscope := (H.scopeWF henv).toCtx
  simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hscope

/-- An expression with a forall binder is a forall, so stripping a top-level type
annotation leaves it unchanged. -/
theorem Expr.ForallBinderAt.consumeTypeAnnotationsVerified_eq_self
    (H : Expr.ForallBinderAt source i domain) :
    (source.consumeTypeAnnotationsVerified annOk) = source := by
  cases H with
  | here => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
  | there _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

/-- Closing a body over a source telescope gives one forall per declaration of the scope,
with the simultaneous abstraction in oldest-first order as residual. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeSource_telescope
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (_hnodup : scope.fvars.Nodup) (body : Expr) :
    Expr.ForallTelescope (H.closeSource body) scope.length
      (body.abstractN scope.fvars.reverse) := by
  clear _hnodup
  induction H generalizing body with
  | nil =>
    have hfvars : (VLCtx.fvars ([] : VLCtx)) = [] := rfl
    simp only [SourceTelescope.closeSource, hfvars, List.reverse_nil,
      Expr.abstractN_nil, List.length_nil]
    exact .nil body
  | @cons scope domainTarget fv deps tail name binderInfo domain Hdomain ih =>
    let innerBody := body.abstractN [fv]
    have Houter := ih (.forallE name domain innerBody binderInfo)
    have Houter' : Expr.ForallTelescope
        (tail.closeSource (.forallE name domain innerBody binderInfo))
        scope.length
        (.forallE name (domain.abstractN scope.fvars.reverse)
          (innerBody.abstractN scope.fvars.reverse 1) binderInfo) := by
      simpa [innerBody, Expr.abstractN] using Houter
    have Hinner : Expr.ForallTelescope
        (.forallE name (domain.abstractN scope.fvars.reverse)
          (innerBody.abstractN scope.fvars.reverse 1) binderInfo)
        1 (innerBody.abstractN scope.fvars.reverse 1) := by
      simpa using Expr.ForallTelescope.cons
        (Expr.ForallTelescope.nil
          (innerBody.abstractN scope.fvars.reverse 1))
    have Hcombined := Houter'.trans Hinner
    have hresidual :
        (body.abstractN [fv]).abstractN scope.fvars.reverse 1 =
          body.abstractN (fv :: scope.fvars).reverse := by
      rw [List.reverse_cons, Expr.abstractN_append]
      rfl
    rw [hresidual] at Hcombined
    simpa [SourceTelescope.closeSource] using Hcombined

/-- Closing a translated type over a source telescope translates to the forall telescope
over the scope's abstract domains, in oldest-first order. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeTranslation
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (Hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    TrExprS env Us [] (H.closeSource body)
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  induction H generalizing body target with
  | nil =>
    change TrExprS env Us [] body target
    exact Hbody
  | @cons scope domainTarget fv deps tail name binderInfo domain Hdomain ih =>
    have HtailWF : scope.WF env Us.length := Hscope.1
    have HdomainType : env.IsType Us.length scope.toCtx domainTarget := by
      exact Hscope.2.2
    have W := abstractForallContext.abstractHead
      ([] : List VExpr) scope fv deps domainTarget
    have HbodyAbstract : TrExprS env Us
        ((none, .vlam domainTarget) :: scope)
        (body.abstract1 fv) target := by
      simpa [abstractForallContext] using Hbody.abstract W
    have Hforall : TrExprS env Us scope
        (.forallE name domain (body.abstract1 fv) binderInfo)
        (.forallE domainTarget target) :=
      .forallE HdomainType HbodyType Hdomain HbodyAbstract
    have HforallType : env.IsType Us.length scope.toCtx
        (.forallE domainTarget target) :=
      VEnv.IsType.forallE HdomainType HbodyType
    have Hclosed := ih HtailWF Hforall HforallType
    have hbodyClosed : Closed body := by
      have h := Hbody.closed
      simpa [VLCtx.bvars, tail.noBV] using h
    have h1 : body.abstractN [fv] = body.abstract1 fv :=
      Expr.abstractN_singleton hbodyClosed.looseBVarRange_le
    simpa [h1, SourceTelescope.closeSource, VLCtx.toCtx,
      List.reverse_cons, VExpr.wrapForalls] using Hclosed

/-- Binder-by-binder form of `closeTranslation`. -/
theorem checkInductiveTypes.loopType.SourceTelescope.closeTypedTelescope
    (H : checkInductiveTypes.loopType.SourceTelescope env Us scope)
    (Hscope : scope.WF env Us.length)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  have Htranslation := H.closeTranslation Hscope Hbody HbodyType
  have Htelescope := H.closeSource_telescope Hscope.fvars_nodup body
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
    apply VEnv.IsType.wrapForalls
    · simpa using Hscope.toCtx
    · simpa using HbodyType
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope Htranslation HtargetType

/-- Binder-by-binder form of `closeTranslation` for a scope embedding: closing a
translated type over the scope (which need not be contiguous) gives a closed typed
telescope. The body may itself be a dependent telescope. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closeTypedTelescope
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF)
    (Hbody : TrExprS env Us scope body target)
    (HbodyType : env.IsType Us.length scope.toCtx target) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sourceTelescope.closeSource body) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse target) := by
  exact H.sourceTelescope.closeTypedTelescope (H.scopeWF henv)
    Hbody HbodyType

/-- Close the source declarations of a scope embedding around `Sort 0`. This is a
translation of the scope's telescope on its own, rather than of a later expression
under it. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closedSortTranslation
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    TrExprS env Us []
      (H.sourceTelescope.closeSource (.sort (.zero : Level)))
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) ∧
    env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
  have HscopeWF := H.scopeWF henv
  have hzero : VLevel.ofLevel Us (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hsort : TrExprS env Us scope (.sort (.zero : Level))
      (.sort (.zero : VLevel)) := .sort hzero
  have HsortType : env.IsType Us.length scope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  have Hclosed := H.sourceTelescope.closeTranslation HscopeWF
    Hsort HsortType
  have HtargetType : env.IsType Us.length []
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    apply VEnv.IsType.wrapForalls
    · simpa using HscopeWF.toCtx
    · simpa using HsortType
  exact ⟨Hclosed, HtargetType⟩

/-- Binder-by-binder form of `closedSortTranslation`. -/
theorem checkInductiveTypes.loopType.ScopeEmbedding.closedSortTelescope
    (H : checkInductiveTypes.loopType.ScopeEmbedding
      env Us scope runtime)
    (henv : env.WF) :
    Expr.ForallTelescopeTypeTranslation env Us []
      (H.sourceTelescope.closeSource (.sort (.zero : Level))) scope.length
      (VExpr.wrapForalls scope.toCtx.reverse
        (.sort (.zero : VLevel))) := by
  rcases H.closedSortTranslation henv with ⟨Htranslation, Htype⟩
  have Htelescope := H.sourceTelescope.closeSource_telescope
    (H.scopeWF henv).fvars_nodup (.sort (.zero : Level))
  have Htelescope' : Expr.ForallTelescope
      (H.sourceTelescope.closeSource (.sort (.zero : Level))) scope.length
      (.sort (.zero : Level)) := by
    have hsort : ∀ fvars : List FVarId,
        (Expr.sort (.zero : Level)).abstractN fvars =
          .sort (.zero : Level) := fun _ => rfl
    rw [hsort] at Htelescope
    exact Htelescope
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope' Htranslation Htype

/-- Binding a list of ordinary local declarations creates one concrete forall
per selected declaration and leaves precisely the simultaneous abstraction of
the selected free variables as its residual body. -/
theorem LocalContext.mkBindingListN_forallTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (LocalContext.mkBindingListN false lctx fvs body)
      fvs.length (body.abstractN fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.ForallTelescope
        (LocalContext.mkBindingListN.go false lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingListN.go]
      have htail := ih
        (LocalContext.mkBindingList1N false lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.ForallTelescope
          (LocalContext.mkBindingList1N false lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1N, hfind]
        exact Expr.ForallTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractN fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- `LocalContext.mkForall` over a list of free variables denoting ordinary declarations
gives a forall telescope with the simultaneous abstraction as residual. -/
theorem LocalContext.mkForall_fvars_forallTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (lctx.mkForall (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractN fvs) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_forallTelescope hdecl

/-- Closing two bodies over the same list of ordinary local declarations
creates the same concrete lambda prefix. -/
theorem LocalContext.sameLambdaPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (left right : Expr) :
    Expr.SameLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) left)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) right) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- Closing one residual with foralls and another with lambdas over the same
ordinary declarations creates one literal cross-kind binder prefix. -/
theorem LocalContext.sameForallLambdaPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) forallBody)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) lambdaBody) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameForallLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- Simultaneous free-variable abstraction raises a closed loose-variable
boundary by exactly the number of introduced binders. -/
theorem Expr.abstractN_looseBVarRange_le
    {e : Expr} {fvs : List FVarId} {k : Nat}
    : (e.abstractN fvs k).looseBVarRange' ≤
        max k e.looseBVarRange' + fvs.length := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstractN, Expr.looseBVarRange']; omega
  | fvar v =>
    simp only [Expr.abstractN]
    split
    · rename_i r hr
      have := Expr.lastRevIdx?_lt_length hr
      simp [Expr.looseBVarRange']; omega
    · simp [Expr.looseBVarRange']
  | mdata _ e ih | proj _ _ e ih => simpa [Expr.abstractN, Expr.looseBVarRange'] using ih
  | app f a ihf iha =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    constructor <;> [have := @ihf k; have := @iha k] <;> omega
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    have h1 := @iht k; have h2 := @ihb (k + 1)
    constructor <;> omega
  | letE _ t v b _ iht ihv ihb =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    have h1 := @iht k; have h2 := @ihv k; have h3 := @ihb (k + 1)
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  | const _ _ | sort _ | mvar _ | lit _ => simp [Expr.abstractN, Expr.looseBVarRange']

/-- Application spines preserve a common loose-variable bound. -/
theorem Expr.mkAppN_looseBVarRange_le
    (Hfn : fn.looseBVarRange' ≤ k)
  (Hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ k) :
    (mkAppN fn args).looseBVarRange' ≤ k := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  have Hlist : ∀ arg ∈ args.toList, arg.looseBVarRange' ≤ k := by
    intro arg harg
    exact Hargs arg (Array.mem_toList_iff.mp harg)
  generalize args.toList = list at Hlist
  induction list generalizing fn with
  | nil => exact Hfn
  | cons arg rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · simpa [Lean.Expr.looseBVarRange', Nat.max_le] using
          And.intro Hfn (Hlist arg (by simp))
      · intro other hother
        exact Hlist other (by simp [hother])

@[simp] theorem Expr.instantiate1'_mkAppN :
    (mkAppN fn args).instantiate1' value k =
      mkAppN (fn.instantiate1' value k)
        (args.map fun arg => arg.instantiate1' value k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  rw [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih (fn := fn.app arg)

@[simp] theorem Expr.getAppFn_liftLooseBVars'
    {e : Expr} {start amount : Nat} :
    (e.liftLooseBVars' start amount).getAppFn =
      e.getAppFn.liftLooseBVars' start amount := by
  induction e generalizing start with
  | app fn arg ih => simpa [Expr.getAppFn, Expr.liftLooseBVars'] using ih
  | _ => rfl

theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_eq_self_of_pos
    (H : Expr.ForallTelescope outer arity body) (hpos : 0 < arity) :
    (outer.consumeTypeAnnotationsVerified annOk) = outer := by
  cases H with
  | nil => simp at hpos
  | cons _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

/-- Removing a possible top-level binder annotation preserves the number of
leading forall binders.  In the zero-binder case the residual may itself be
the annotation payload, so it is retained existentially. -/
theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_arity
    (H : Expr.ForallTelescope outer arity body) :
    ∃ residual, Expr.ForallTelescope (outer.consumeTypeAnnotationsVerified annOk)
      arity residual := by
  cases H with
  | nil => exact ⟨_, .nil _⟩
  | @cons body arity result name dom bi Htail =>
      have houter :
          ((Expr.forallE name dom body bi).consumeTypeAnnotationsVerified annOk) =
            Expr.forallE name dom body bi := by
        apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
      exact ⟨_, houter ▸ Expr.ForallTelescope.cons Htail⟩

theorem Expr.AvoidingLambdaTelescope.abstract1
    (H : Expr.AvoidingLambdaTelescope names outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.AvoidingLambdaTelescope names (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons hdom H ih =>
    simp only [Expr.abstract1]
    apply Expr.AvoidingLambdaTelescope.cons (hdom.abstract1 fv k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- `LocalContext.mkLambda` over a list of free variables denoting ordinary declarations
gives a lambda telescope with the simultaneous abstraction as residual. -/
theorem LocalContext.mkBindingListN_lambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (LocalContext.mkBindingListN true lctx fvs body)
      fvs.length (body.abstractN fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.LambdaTelescope
        (LocalContext.mkBindingListN.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingListN.go]
      have htail := ih
        (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.LambdaTelescope
          (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1N, hfind]
        exact Expr.LambdaTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractN fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

theorem LocalContext.mkBindingListN_avoidingLambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (havoid : ∀ fv index name type bi kind,
      fv ∈ fvs →
      lctx.find? fv = some (.cdecl index fv name type bi kind) →
      type.AvoidsConsts namesToAvoid) :
    Expr.AvoidingLambdaTelescope namesToAvoid
      (LocalContext.mkBindingListN true lctx fvs body)
      fvs.length (body.abstractN fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      xs ⊆ fvs →
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.AvoidingLambdaTelescope namesToAvoid
        (LocalContext.mkBindingListN.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _ _
      exact .nil _
    | cons fv xs ih =>
      intro current hsubset hxs
      rw [LocalContext.mkBindingListN.go]
      have htail := ih
        (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
        (fun x hx => hsubset (by simp [hx]))
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.AvoidingLambdaTelescope namesToAvoid
          (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1N, hfind]
        apply Expr.AvoidingLambdaTelescope.cons
        · exact (havoid fv index name type bi kind
            (hsubset (by simp)) hfind).abstractN xs.reverse
        · exact .nil _
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractN fvs) (by simp)
      (fun fv hfv => hdecl fv (by simpa using hfv))

theorem LocalContext.mkLambda_fvars_lambdaTelescopeN
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractN fvs) := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_lambdaTelescope hdecl

/-- Sequential-model form of `mkLambda_fvars_lambdaTelescopeN`, valid for locally closed
bodies and duplicate-free variable lists. -/
theorem LocalContext.mkLambda_fvars_lambdaTelescopeList
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvs.Nodup) (hb : Closed body) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed hnodup hb]
  exact LocalContext.mkLambda_fvars_lambdaTelescopeN hdecl

theorem LocalContext.mkBindingListN_append_four
    (hdecl : ∀ fv ∈ ((as ++ bs) ++ cs) ++ ds,
      ∃ decl, lctx.find? fv = some decl)
    (hnodup : (((as ++ bs) ++ cs) ++ ds).Nodup) :
    LocalContext.mkBindingListN isLambda lctx
        (((as ++ bs) ++ cs) ++ ds) body =
      LocalContext.mkBindingListN isLambda lctx as
        (LocalContext.mkBindingListN isLambda lctx bs
          (LocalContext.mkBindingListN isLambda lctx cs
            (LocalContext.mkBindingListN isLambda lctx ds body))) := by
  have habcd := List.nodup_append.mp hnodup
  have habc := List.nodup_append.mp habcd.1
  have hab := List.nodup_append.mp habc.1
  have hasDecl : ∀ fv ∈ as, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hbsDecl : ∀ fv ∈ bs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hcsDecl : ∀ fv ∈ cs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hdsDecl : ∀ fv ∈ ds, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  rw [LocalContext.mkBindingListN_eq_fold hdecl hnodup,
    LocalContext.mkBindingListN_eq_fold hasDecl hab.1,
    LocalContext.mkBindingListN_eq_fold hbsDecl hab.2.1,
    LocalContext.mkBindingListN_eq_fold hcsDecl habc.2.1,
    LocalContext.mkBindingListN_eq_fold hdsDecl habcd.2.1]
  simp only [List.foldr_append]

/-- A selected executable array consists solely of ordinary free-variable
declarations in the retained local context. -/
structure CDeclArray (lctx : LocalContext) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  declarations : ∀ fv ∈ fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

/-- `LocalContext.mkLambda` uses one literal binder prefix for any two
residual bodies when it closes the same duplicate-free local selection. -/
theorem CDeclArray.sameLambdaPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameLambdaPrefix xs.size
      (lctx.mkLambda xs left) (lctx.mkLambda xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkLambda, LocalContext.mkLambda,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameLambdaPrefixN_fold hdecl left right

/-- `mkForall` and `mkLambda` close two residuals with the same literal
ordinary-declaration prefix when they use the same duplicate-free local
selection. -/
theorem CDeclArray.sameForallLambdaPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix xs.size
      (lctx.mkForall xs forallBody) (lctx.mkLambda xs lambdaBody) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkLambda,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallLambdaPrefixN_fold hdecl
    forallBody lambdaBody

/-- An array of free variables, each a member of the local context of `c`. Membership is
preserved when the recursor construction adds binders. -/
structure FVarArrayIn (c : AddInductive.Context) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  members : ∀ fv ∈ fvars, fv ∈ c.lctx.fvars

def recursorFVarId : Expr → FVarId
  | .fvar fv => fv
  | _ => default

def ExprArrayFVarIds (xs : Array Expr) : List FVarId :=
  xs.toList.map recursorFVarId

theorem cachedParameterDecls_fvars
    {decls : VLCtx}
    (H : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl params decls) :
    ∃ fvars : List FVarId,
      params = fvars.map Expr.fvar ∧ decls.fvars = fvars := by
  induction H with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons param entry params decls Hhead _ ih =>
    rcases Hhead with ⟨fv, deps, type, rfl, rfl⟩
    rcases ih with ⟨fvars, hparams, hdecls⟩
    exact ⟨fv :: fvars, by simp [hparams], by simp [hdecls]⟩

/-- The declaration order of the retained parameter suffix is the reverse of
the executable parameter array's free-variable order. -/
theorem RecursorParameterContextSuffix.parameterDecls_fvars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    H.parameterDecls.fvars = (ExprArrayFVarIds stats.params).reverse := by
  rcases cachedParameterDecls_fvars H.cached with
    ⟨fvars, hparams, hdecls⟩
  rw [hdecls]
  have hids := congrArg (List.map recursorFVarId) hparams
  simpa [ExprArrayFVarIds, List.map_reverse, Function.comp_def,
    recursorFVarId] using hids.symm

/-- Close the cached parameter suffix outside an anonymous inner telescope. The source
parameter order is that of the parameter array used by the recursor construction, and the
abstract domains are those cached by the header phase. -/
theorem RecursorParameterContextSuffix.abstractParameters
    {c root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (Hparams : FVarArrayIn root stats.params)
    (hnodup : Hparams.fvars.Nodup)
    (Htr : TrExprS env Us
      (abstractForallContext domains H.parameterDecls) source target) :
    TrExprS env Us
      (abstractForallContext
        (H.parameterDecls.toCtx.reverse ++ domains) [])
      (source.abstractList Hparams.fvars domains.length) target := by
  have hparamExprs : stats.params.toList.reverse =
      Hparams.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList Hparams.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have Hcached : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl
      (Hparams.fvars.reverse.map Expr.fvar) H.parameterDecls := by
    have Hbase := H.cached
    rw [hparamExprs] at Hbase
    exact Hbase
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      Hparams.fvars.reverse H.parameterDecls := by
    rw [List.forall₂_map_left_iff] at Hcached
    exact Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have Hclosed := TrExprS.abstractFVarLambdaSuffix
    (domains := domains) Hdecls
      (List.nodup_reverse.mpr hnodup) Htr
  simp only [List.reverse_reverse] at Hclosed
  simpa using Hclosed

/-- The cached parameters form a dependency-closed subset (an up-set) of the recursor
context: motives and minors are newer ambient declarations, so no parameter depends on
them. -/
theorem RecursorParameterContextSuffix.parameterFVarsUp
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    IsFVarUpSet (fun fv => fv ∈ ExprArrayFVarIds stats.params)
      R.mlctx.vlctx := by
  have hwf : VLCtx.WF R.venv recLparams.length
      (H.ambientDecls ++ H.parameterDecls) := by
    rw [← H.context]
    exact R.mlctx_wf.tr.wf
  have hcached := IsFVarUpSet.suffixFVars H.parameterDecls
    H.ambientDecls hwf
  have hcongr : ∀ fv ∈
      (H.ambientDecls ++ H.parameterDecls).fvars,
      fv ∈ H.parameterDecls.fvars ↔
        fv ∈ ExprArrayFVarIds stats.params := by
    intro fv _
    rw [H.parameterDecls_fvars]
    simp
  have hconverted :=
    (IsFVarUpSet.congr hwf.fvwf hcongr).mp hcached
  simpa [H.context] using hconverted

/-- Typed form of `closedSortTranslation`: the closed parameter telescope translates and
is a type, so its domains can be opened as the base context of a later telescope. -/
theorem RecursorParameterContextSuffix.closedSortTyped
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    TrExprS R.venv recLparams []
        (R.mlctx.lctx.mkForall stats.params
          (.sort (.zero : Level)))
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) ∧
      R.venv.IsType recLparams.length []
        (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) := by
  let parameterMLCtx := R.mlctx.dropN depth H.depth_le
  have hparameterWF : parameterMLCtx.WF R.venv recLparams := by
    simpa [parameterMLCtx] using R.mlctx_wf.dropN depth H.depth_le
  have hparameterOnly : MLCtxOnlyLams parameterMLCtx := by
    simpa [parameterMLCtx] using R.onlyLams.dropN depth H.depth_le
  have hparameterCtx : parameterMLCtx.vlctx = H.parameterDecls := by
    simpa [parameterMLCtx] using H.dropAmbient_vlctx
  have hparams : stats.params.toList.reverse =
      (parameterMLCtx.fvarRevList parameterMLCtx.length
        (Nat.le_refl _)).map Expr.fvar := by
    rcases cachedParameterDecls_fvars H.cached with
      ⟨fvars, hsource, hscope⟩
    rw [TypeChecker.MLCtx.fvarRevList_all, hparameterCtx, hscope]
    exact hsource
  have hparamsArray : stats.params =
      (parameterMLCtx.vlctx.fvars.reverse.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    rw [TypeChecker.MLCtx.fvarRevList_all] at hparams
    have hforward := congrArg List.reverse hparams
    simpa [List.map_reverse] using hforward
  have hlocalSource : R.mlctx.lctx.mkForall stats.params
        (.sort (.zero : Level)) =
      parameterMLCtx.lctx.mkForall stats.params
        (.sort (.zero : Level)) := by
    rw [hparamsArray, LocalContext.mkForall, LocalContext.mkForall,
      LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN]
    apply LocalContext.mkBindingListN_congr
    intro fv hfv
    apply R.onlyLams.dropN_find?_eq R.mlctx_wf depth H.depth_le
    exact List.mem_reverse.mp hfv
  have hsource : parameterMLCtx.lctx.mkForall stats.params
        (.sort (.zero : Level)) =
      parameterMLCtx.mkForall parameterMLCtx.length (Nat.le_refl _)
        (.sort (.zero : Level)) :=
    hparameterWF.mkForall_eq parameterMLCtx.length (Nat.le_refl _) hparams trivial
  have hzero : VLevel.ofLevel recLparams (.zero : Level) =
      some (.zero : VLevel) := rfl
  have hsort : TrExprS R.venv recLparams parameterMLCtx.vlctx
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) := .sort hzero
  have hsortType : R.venv.IsType recLparams.length
      parameterMLCtx.vlctx.toCtx (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  have hclosed := hparameterWF.mkForall_trS R.checking.tr.wf
    hsort hsortType parameterMLCtx.length (Nat.le_refl _)
  have hdomains := hparameterOnly.forallDomains_eq_take_reverse
    parameterMLCtx.length (Nat.le_refl _)
  have hparameterLength : parameterMLCtx.length =
      H.parameterDecls.length := by
    rw [← TypeChecker.MLCtx.vlctx_length, hparameterCtx]
  have htake : H.parameterDecls.toCtx.take parameterMLCtx.length =
      H.parameterDecls.toCtx := by
    have htoCtxLength : H.parameterDecls.toCtx.length =
        H.parameterDecls.length :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        H.cached
    apply List.take_of_length_le
    rw [htoCtxLength, ← hparameterLength]
    exact Nat.le_refl _
  rw [TypeChecker.MLCtx.dropN_all, ← hsource] at hclosed
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, hdomains] at hclosed
  rw [hparameterCtx, htake] at hclosed
  rw [hlocalSource]
  exact hclosed

/-- `Sort 0` closed over the cached parameter declarations translates. This gives a
translation of the parameter telescope on its own, whose prefix can be compared with any
executable telescope closed over the same parameters. -/
theorem RecursorParameterContextSuffix.closedSortTranslation
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    TrExprS R.venv recLparams []
      (R.mlctx.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) :=
  H.closedSortTyped.1

/-- The parameter array `stats.params` used by `mkRecInfos` is an array of free variables
of the header context. -/
def checkInductiveTypes.loopType.ParameterContextSuffix.paramsBound
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc stats depth) :
    FVarArrayIn c stats.params := by
  refine {
    fvars := ExprArrayFVarIds stats.params
    expressions := ?_
    members := ?_ }
  · rw [← Array.toList_inj]
    rcases cachedParameterDecls_fvars H.cached with
      ⟨reversedFVars, hparamsRev, hscopeFVars⟩
    have hreverse := congrArg List.reverse hparamsRev
    have hparams : stats.params.toList =
        reversedFVars.reverse.map Expr.fvar := by
      simpa [List.map_reverse] using hreverse
    change stats.params.toList =
      (ExprArrayFVarIds stats.params).map Expr.fvar
    rw [ExprArrayFVarIds, hparams]
    simp [recursorFVarId, Function.comp_def]
  · intro fv hfv
    rcases cachedParameterDecls_fvars H.cached with
      ⟨reversedFVars, hparamsRev, hscopeFVars⟩
    have hreverse := congrArg List.reverse hparamsRev
    have hparams : stats.params.toList =
        reversedFVars.reverse.map Expr.fvar := by
      simpa [List.map_reverse] using hreverse
    have hparameter : fv ∈ H.parameterDecls.fvars := by
      rw [hscopeFVars]
      change fv ∈ ExprArrayFVarIds stats.params at hfv
      rw [ExprArrayFVarIds, hparams] at hfv
      simpa [recursorFVarId, Function.comp_def] using hfv
    have hfull : fv ∈ Hc.mlctx.vlctx.fvars := by
      rw [H.context, VLCtx.fvars_append]
      exact List.mem_append_right _ hparameter
    rw [← Hc.mlctx_wf.tr.fvars_eq, Hc.lctx_eq] at hfull
    exact hfull

theorem checkInductiveTypes.loopType.ParameterContextSuffix.paramsBound_nodup
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc stats depth) :
    (H.paramsBound (c := c)).fvars.Nodup := by
  change (ExprArrayFVarIds stats.params).Nodup
  rcases cachedParameterDecls_fvars H.cached with
    ⟨reversedFVars, hparamsRev, hscopeFVars⟩
  have hreverse := congrArg List.reverse hparamsRev
  have hparams : stats.params.toList =
      reversedFVars.reverse.map Expr.fvar := by
    simpa [List.map_reverse] using hreverse
  have hfull := Hc.mlctx_wf.fvars_nodup
  rw [H.context, VLCtx.fvars_append] at hfull
  have hparameter : H.parameterDecls.fvars.Nodup :=
    (List.nodup_append.mp hfull).2.1
  rw [hscopeFVars] at hparameter
  rw [ExprArrayFVarIds, hparams]
  simpa [recursorFVarId, Function.comp_def] using
    (List.nodup_reverse.2 hparameter)

structure BindingContextLE (c c' : AddInductive.Context) : Prop where
  fvars : c.lctx.fvars ⊆ c'.lctx.fvars
  declarations : ∀ fv ∈ c.lctx.fvars,
    c'.lctx.find? fv = c.lctx.find? fv
  env_eq : c'.env = c.env
  lparams_eq : c'.lparams = c.lparams
  safety_eq : c'.safety = c.safety
  allowPrimitive_eq : c'.allowPrimitive = c.allowPrimitive
  fuel_eq : c'.fuel = c.fuel

instance : CoeFun (BindingContextLE c c') fun _ =>
    ∀ ⦃fv⦄, fv ∈ c.lctx.fvars → fv ∈ c'.lctx.fvars where
  coe H := H.fvars

theorem BindingContextLE.refl (c : AddInductive.Context) :
    BindingContextLE c c :=
  ⟨fun _ => id, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Changing only the checker context keeps the binding context. -/
theorem BindingContextLE.checkLCtx (c : AddInductive.Context) (l : LocalContext) :
    BindingContextLE { c with checkLCtx := l } c :=
  ⟨fun _ => id, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BindingContextLE.checkLCtx_rev (c : AddInductive.Context) (l : LocalContext) :
    BindingContextLE c { c with checkLCtx := l } :=
  ⟨fun _ => id, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BindingContextLE.trans
    (H₁ : BindingContextLE c₁ c₂) (H₂ : BindingContextLE c₂ c₃) :
    BindingContextLE c₁ c₃ :=
  ⟨fun _ h => H₂ (H₁ h),
    fun fv hfv => (H₂.declarations fv (H₁ hfv)).trans
      (H₁.declarations fv hfv),
    H₂.env_eq.trans H₁.env_eq,
    H₂.lparams_eq.trans H₁.lparams_eq,
    H₂.safety_eq.trans H₁.safety_eq,
    H₂.allowPrimitive_eq.trans H₁.allowPrimitive_eq,
    H₂.fuel_eq.trans H₁.fuel_eq⟩

/-- `BindingContextLE` records the executable fields that affect local
binder identity and lookup.  The embedded typechecker's active universe
parameter list is tracked separately by `RecursorContextWF`, so changing it
on either endpoint preserves this relation definitionally. -/
theorem BindingContextLE.rebaseTypeCheckerLParams
    (H : BindingContextLE c c')
    (lparams lparams' : Option (List Name)) :
    BindingContextLE
      { c with typeCheckerLParams := lparams }
      { c' with typeCheckerLParams := lparams' } :=
  ⟨H.fvars, H.declarations, H.env_eq, H.lparams_eq, H.safety_eq,
    H.allowPrimitive_eq, H.fuel_eq⟩

theorem MLCtxTopAgree.mkForall_eq {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (ha : n ≤ a.length) (hb : n ≤ b.length)
    (e : Expr) : a.mkForall n ha e = b.mkForall n hb e := by
  induction H generalizing e with
  | zero => simp
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.mkForall]
    exact ih _ _ _

theorem MLCtxTopAgree.forallTelescope {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ {W : Expr} {k : Nat} {rW : Expr}, Expr.ForallTelescope W k rW →
      ∃ r, Expr.ForallTelescope (b.mkForall n hb W) (n + k) r := by
  induction H with
  | zero => intro W k rW HW; exact ⟨rW, by simpa using HW⟩
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro W k rW HW
    simp only [TypeChecker.MLCtx.mkForall]
    have Habs := HW.abstract1 fv 0
    have Hcons : Expr.ForallTelescope
        (.forallE name ty (W.abstract1 fv) bi) (k + 1)
        (rW.abstract1 fv (0 + k)) := .cons Habs
    obtain ⟨r, Hr⟩ := ih (Nat.le_of_succ_le_succ hb) Hcons
    exact ⟨r, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hr⟩

theorem MLCtxTopAgree.binderAt_shift {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ {j : Nat} {d : Expr}, ∃ d', ∀ W : Expr, Expr.ForallBinderAt W j d →
      Expr.ForallBinderAt (b.mkForall n hb W) (n + j) d' := by
  induction H with
  | zero => intro j d; exact ⟨d, fun W h => by simpa using h⟩
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro j d
    obtain ⟨d', Hd'⟩ := ih (Nat.le_of_succ_le_succ hb)
      (j := j + 1) (d := d.abstract1 fv j)
    refine ⟨d', fun W HW => ?_⟩
    simp only [TypeChecker.MLCtx.mkForall]
    have Habs := HW.abstract1 fv 0
    have Hthere : Expr.ForallBinderAt
        (.forallE name ty (W.abstract1 fv) bi) (j + 1) (d.abstract1 fv j) := by
      simpa using Expr.ForallBinderAt.there (name := name)
        (outerDomain := ty) (bi := bi) Habs
    have := Hd' _ Hthere
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem MLCtxTopAgree.binderAt_indep {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hb : n ≤ b.length) :
    ∀ i < n, ∃ d, ∀ W : Expr, Expr.ForallBinderAt (b.mkForall n hb W) i d := by
  induction H with
  | zero => intro i hi; omega
  | vlam h fv name ty t₁ t₂ bi ih =>
    intro i hi
    simp only [TypeChecker.MLCtx.mkForall]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨d, Hd⟩ := ih (Nat.le_of_succ_le_succ hb) i hi
      exact ⟨d, fun W => Hd _⟩
    · obtain ⟨d', Hd'⟩ := MLCtxTopAgree.binderAt_shift h
        (Nat.le_of_succ_le_succ hb) (j := 0) (d := ty)
      refine ⟨d', fun W => ?_⟩
      simpa using Hd' _ (Expr.ForallBinderAt.here (name := name)
        (domain := ty) (body := W.abstract1 fv) (bi := bi))

end VerifyInductive
end Lean4Lean
