import Lean4Lean.Verify.Inductive.Recursor.Context.FVarArrays

/-! The types the executable passes to `withLocalDecl` for the recursor binders and
their translations (`FVarDeclAt`, `FVarArrayBinderTypes`, `TrBinderTypes`), the
constructor application typing `ConstructorApplicationAt`, and the input and run
relations of `loopUArgs` (`LoopUArgsInput`, `LoopUArgsRun`). Part of the recursor
phase (section 3.2 of the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Declarative typing of the constructor application at the end of a
constructor traversal, used by the minor pass.  It records the terminal
source expression and the generated constructor application, so that recursor
generation does not depend on a second executable classification. -/
structure ConstructorApplicationAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (ctor : Constructor)
    (terminal : Expr) (allFields : Array Expr)
    (terminalTarget : VExpr) : Type where
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats terminal = some ownerIdx
  terminal_type : R.venv.IsType recLparams.length
    R.mlctx.vlctx.toCtx terminalTarget
  introTarget : VExpr
  intro : TrExprS R.venv recLparams R.mlctx.vlctx
    (mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
    introTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    introTarget terminalTarget

/-- Translations of an executable binder-type array under the
recursor universe list.  This is the universe-parametric counterpart of
`TranslatedOriginTypes`, used for major and motive rows after large
elimination has made `ContextWF` unavailable. -/
structure TrBinderTypes
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (origins : Array Expr) where
  targets : List VExpr
  translated : List.Forall₂
    (TrExprS R.venv recLparams R.mlctx.vlctx) origins.toList targets
  isType : ∀ target ∈ targets,
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx target

def TrBinderTypes.empty
    (R : RecursorContextWF c recLparams) :
    TrBinderTypes R #[] where
  targets := []
  translated := .nil
  isType _ h := by simp at h

/-- Weaken an entire translated binder-type row along an arbitrary
recursor-context extension.  Constructor fields, generated hypotheses, and
minor premises are introduced in separate traversals, so their composite
extension is more useful here than a consecutive-suffix specialization. -/
def TrBinderTypes.mono
    (H : TrBinderTypes Rroot origins)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    TrBinderTypes Rcurrent origins where
  targets := H.targets.map fun target =>
    target.lift' (Hext.shift.consN 0)
  translated := by
    apply checkPositivityStep.forall₂_map_right H.translated
    intro source target Hsource
    exact Hext.weakTrExprS Hsource
  isType := by
    intro target htarget
    rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
    exact Hext.weakIsType (H.isType oldTarget hold)

/-- Weaken an existing binder-type row through one newly checked recursor
local without appending a new row entry. -/
def TrBinderTypes.withLocalDecl
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {origins : Array Expr}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : TrBinderTypes R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    TrBinderTypes R' origins := by
  dsimp only
  let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
    (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  exact {
    targets := H.targets.map fun target => target.liftN 1 0
    translated := by
      apply checkPositivityStep.forall₂_map_right H.translated
      intro source target Hsource
      exact Hsource.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
    isType := by
      intro target htarget
      rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
      exact (H.isType oldTarget hold).weakN R.checking.tr.wf.ordered W.toCtx }

/-- Append a newly checked binder type while weakening all older entries
through its declaration. -/
def TrBinderTypes.push
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {origins : Array Expr}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : TrBinderTypes R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    TrBinderTypes R' (origins.push ty) := by
  dsimp only
  let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
    (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  let liftedTargets := H.targets.map fun target => target.liftN 1 0
  exact {
    targets := liftedTargets ++ [ty'.liftN 1 0]
    translated := by
      rw [Array.toList_push]
      apply List.Forall₂.append'
      · apply checkPositivityStep.forall₂_map_right H.translated
        intro source target Hsource
        exact Hsource.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
      · exact .cons
          (htr.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf) .nil
    isType := by
      intro target htarget
      simp only [liftedTargets, List.mem_append, List.mem_map,
        List.mem_singleton] at htarget
      rcases htarget with ⟨oldTarget, hold, rfl⟩ | rfl
      · exact (H.isType oldTarget hold).weakN
          R.checking.tr.wf.ordered W.toCtx
      · exact hty.weakN R.checking.tr.wf.ordered W.toCtx }

/-- Variant of `TrBinderTypes.push` for a binder opened in both contexts. -/
def TrBinderTypes.pushChecked
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {origins : Array Expr}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : TrBinderTypes R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    {ty₀ : VExpr}
    (htr₀ : TrExprS R.venv recLparams R.chk.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx ty₀) :
    let R' := R.withCheckedLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty htr₀ hty₀
    TrBinderTypes R' (origins.push ty) := by
  dsimp only
  let R' := R.withCheckedLocalDecl (c := c) (recLparams := recLparams)
    (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty htr₀ hty₀
  let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  let liftedTargets := H.targets.map fun target => target.liftN 1 0
  exact {
    targets := liftedTargets ++ [ty'.liftN 1 0]
    translated := by
      rw [Array.toList_push]
      apply List.Forall₂.append'
      · apply checkPositivityStep.forall₂_map_right H.translated
        intro source target Hsource
        exact Hsource.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
      · exact .cons
          (htr.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf) .nil
    isType := by
      intro target htarget
      simp only [liftedTargets, List.mem_append, List.mem_map,
        List.mem_singleton] at htarget
      rcases htarget with ⟨oldTarget, hold, rfl⟩ | rfl
      · exact (H.isType oldTarget hold).weakN
          R.checking.tr.wf.ordered W.toCtx
      · exact hty.weakN R.checking.tr.wf.ordered W.toCtx }

/-- Weaken a binder-type row across the consecutive index suffix
opened since `Rroot`. -/
def TrBinderTypes.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {indices : Array Expr}
    (H : TrBinderTypes Rroot origins)
    (Hrecent : RecursorFVarSuffix Rroot R indices) :
    TrBinderTypes R origins := by
  let W := R.onlyLams.dropN_fvlift indices.size Hrecent.size_le
  refine {
    targets := H.targets.map fun target => target.liftN indices.size 0
    translated := ?_
    isType := ?_ }
  · apply checkPositivityStep.forall₂_map_right H.translated
    intro source target Hsource
    have Hsource' : TrExprS R.venv recLparams
        (R.mlctx.dropN indices.size Hrecent.size_le).vlctx source target := by
      simpa only [Hrecent.venv_eq, Hrecent.drop_eq] using Hsource
    exact Hsource'.weakFV R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
  · intro target htarget
    rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
    have htype : R.venv.IsType recLparams.length
        (R.mlctx.dropN indices.size Hrecent.size_le).vlctx.toCtx
        oldTarget := by
      simpa only [Hrecent.venv_eq, Hrecent.drop_eq] using H.isType _ hold
    exact htype.weakN R.checking.tr.wf.ordered W.toCtx

/-- Row-wise translations of the per-family binder-type arrays recorded
by `RecInfoBinderTypes`. -/
structure TrBinderTypesPerFamily
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (origins : Array (Array Expr)) where
  rows : ∀ i (hi : i < origins.size),
    TrBinderTypes R origins[i]

def TrBinderTypesPerFamily.empty
    (R : RecursorContextWF c recLparams) :
    TrBinderTypesPerFamily R #[] where
  rows i hi := by simp at hi

/-- Row-wise form of `TrBinderTypes.mono`. -/
def TrBinderTypesPerFamily.mono
    (H : TrBinderTypesPerFamily Rroot origins)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    TrBinderTypesPerFamily Rcurrent origins where
  rows i hi := (H.rows i hi).mono Hext

/-- Weaken every binder-type row through one checked local. -/
def TrBinderTypesPerFamily.withLocalDecl
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {origins : Array (Array Expr)}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : TrBinderTypesPerFamily R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    TrBinderTypesPerFamily R' origins := by
  dsimp only
  exact {
    rows := fun i hi => (H.rows i hi).withLocalDecl htr hty }

/-- Weaken every row across the consecutive index suffix introduced
since the root recursor context. -/
def TrBinderTypesPerFamily.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {indices : Array Expr}
    (H : TrBinderTypesPerFamily Rroot origins)
    (Hrecent : RecursorFVarSuffix Rroot R indices) :
    TrBinderTypesPerFamily R origins where
  rows i hi := (H.rows i hi).weakenRecent Hrecent

/-- Append one fully translated family row without changing the ambient
recursor context. -/
def TrBinderTypesPerFamily.push
    (H : TrBinderTypesPerFamily R origins)
    (Hrow : TrBinderTypes R row) :
    TrBinderTypesPerFamily R (origins.push row) where
  rows i hi := by
    by_cases hold : i < origins.size
    · simpa only [Array.getElem_push_lt hold] using H.rows i hold
    · have hieq : i = origins.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      simpa using Hrow

def FVarArrayIn.get
    (H : FVarArrayIn c xs) (i : Nat) (hi : i < xs.size) :
    FVarArrayIn c #[xs[i]] := by
  rcases H with ⟨fvars, rfl, members⟩
  let fv := fvars[i]'(by simpa using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · simp [fv]
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact members fv (List.getElem_mem (by simpa using hi))

/-- Every indexed entry of a bound-fvar array is literally a free variable
present in the executable local context. -/
theorem FVarArrayIn.get_eq_fvar
    (H : FVarArrayIn c xs) (i : Nat) (hi : i < xs.size) :
    ∃ fv, xs[i] = .fvar fv ∧ fv ∈ c.lctx.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  have hifvars : i < fvars.length := by simpa using hi
  refine ⟨fvars[i], ?_, members fvars[i] (List.getElem_mem hifvars)⟩
  simp

/-- The free variable at one array position together with the
ordinary local declaration which introduced it. -/
structure FVarDeclAt
    (c : AddInductive.Context) (xs : Array Expr) (i : Nat) where
  inBounds : i < xs.size
  fvar : FVarId
  expression : xs[i] = .fvar fvar
  member : fvar ∈ c.lctx.fvars
  index : Nat
  userName : Name
  type : Expr
  binderInfo : BinderInfo
  kind : LocalDeclKind
  declaration : c.lctx.find? fvar = some
    (.cdecl index fvar userName type binderInfo kind)

/-- Declared types of a closed local context have no loose bound
variables. -/
theorem FVarDeclAt.closed (D : FVarDeclAt c xs i)
    (hl : LocalContext.LctxClosed c.lctx) : Closed D.type :=
  hl.cdecl D.declaration

theorem FVarArrayIn.declarationAt
    (H : FVarArrayIn c xs) (Hc : BindingContextWF c)
    (i : Nat) (hi : i < xs.size) :
    Nonempty (FVarDeclAt c xs i) := by
  rcases H.get_eq_fvar i hi with ⟨fv, hexpression, hfv⟩
  rcases Hc.findCDecl fv hfv with
    ⟨index, userName, type, binderInfo, kind, hdeclaration⟩
  exact ⟨{
    inBounds := hi
    fvar := fv
    expression := hexpression
    member := hfv
    index := index
    userName := userName
    type := type
    binderInfo := binderInfo
    kind := kind
    declaration := hdeclaration }⟩

/-- The declaration of an array entry survives a binding-context
extension.  In particular the declaration type cannot change while
the free variable is threaded through later `mkRecInfos` passes. -/
def FVarDeclAt.mono
    (D : FVarDeclAt c xs i) (H : BindingContextLE c c') :
    FVarDeclAt c' xs i where
  inBounds := D.inBounds
  fvar := D.fvar
  expression := D.expression
  member := H D.member
  index := D.index
  userName := D.userName
  type := D.type
  binderInfo := D.binderInfo
  kind := D.kind
  declaration := by
    rw [H.declarations D.fvar D.member]
    exact D.declaration

def FVarDeclAt.pushArray
    (D : FVarDeclAt c xs i) (value : Expr) :
    FVarDeclAt c (xs.push value) i where
  inBounds := by
    simp only [Array.size_push]
    have := D.inBounds
    omega
  fvar := D.fvar
  expression := by
    rw [Array.getElem_push_lt D.inBounds]
    exact D.expression
  member := D.member
  index := D.index
  userName := D.userName
  type := D.type
  binderInfo := D.binderInfo
  kind := D.kind
  declaration := D.declaration

/-- Parallel binder types for a free-variable array.  Unlike plain
`FVarArrayIn`, this structure records the exact type used at each
`withLocalDecl`, and the strengthened context-extension relation makes that
fact stable in all later contexts. -/
structure FVarArrayBinderTypes (c : AddInductive.Context)
    (xs origins : Array Expr) where
  bound : FVarArrayIn c xs
  size_eq : origins.size = xs.size
  declaration : ∀ i (_hi : i < xs.size),
    ∃ D : FVarDeclAt c xs i, D.type = origins[i]!

/-- Translations of the declared binder types in
the current executable context.  Targets are stored explicitly because
later recursor restoration must weaken them beneath subsequently introduced
mutual binders. -/
structure TranslatedOriginTypes (Hc : ContextWF c)
    (origins : Array Expr) where
  targets : List VExpr
  translated : List.Forall₂
    (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
    origins.toList targets
  isType : ∀ target ∈ targets,
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx target

def TranslatedOriginTypes.empty (Hc : ContextWF c) :
    TranslatedOriginTypes Hc #[] where
  targets := []
  translated := .nil
  isType _ h := by simp at h

/-- Two declarations for the same expression in one local context
have the same declaration type.  This permits different source
arrays and indices: the free-variable identity, rather than an incidental
array presentation, determines the local declaration. -/
theorem FVarDeclAt.type_eq_of_expression
    (D : FVarDeclAt c xs i)
    (E : FVarDeclAt c ys j)
    (hexpression : xs[i]'D.inBounds = ys[j]'E.inBounds) :
    D.type = E.type := by
  have hfvarExpr : Expr.fvar D.fvar = Expr.fvar E.fvar :=
    D.expression.symm.trans (hexpression.trans E.expression)
  have hfvar : D.fvar = E.fvar := Expr.fvar.inj hfvarExpr
  have hdeclaration := E.declaration
  rw [← hfvar, D.declaration] at hdeclaration
  exact congrArg LocalDecl.type (Option.some.inj hdeclaration)

/-- Recover the executable binder type from any `FVarDeclAt` for
the same array position. -/
theorem FVarArrayBinderTypes.type_eq
    (H : FVarArrayBinderTypes c xs origins)
    (D : FVarDeclAt c xs i) :
    D.type = origins[i]! := by
  rcases H.declaration i D.inBounds with ⟨E, htype⟩
  exact (D.type_eq_of_expression E (by rfl)).trans htype

def FVarArrayBinderTypes.empty (c : AddInductive.Context) :
    FVarArrayBinderTypes c #[] #[] where
  bound := FVarArrayIn.empty c
  size_eq := rfl
  declaration i hi := by simp at hi

def FVarArrayBinderTypes.mono
    (H : FVarArrayBinderTypes c xs origins)
    (hle : BindingContextLE c c') :
    FVarArrayBinderTypes c' xs origins where
  bound := H.bound.mono hle
  size_eq := H.size_eq
  declaration i hi := by
    rcases H.declaration i hi with ⟨D, htype⟩
    exact ⟨D.mono hle, htype⟩

def FVarArrayBinderTypes.pushCurrent
    (H : FVarArrayBinderTypes c xs origins)
    (Hc : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FVarArrayBinderTypes
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) (origins.push ty) := by
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  refine {
    bound := H.bound.pushCurrent name ty bi
    size_eq := by simpa using H.size_eq
    declaration := ?_ }
  intro i hi
  by_cases hilast : i = xs.size
  · subst i
    let D : FVarDeclAt c'
        (xs.push (.fvar ⟨c.ngen.curr⟩)) xs.size := {
      inBounds := by simp
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    refine ⟨D, ?_⟩
    change ty = (origins.push ty)[xs.size]!
    rw [show xs.size = origins.size from H.size_eq.symm]
    simp
  · have hiOld : i < xs.size := by
      have : i < xs.size + 1 := by simpa using hi
      omega
    rcases H.declaration i hiOld with ⟨D, htype⟩
    refine ⟨(D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep, ?_⟩
    have hsizes := H.size_eq
    have hiOrigins : i < origins.size := by omega
    change D.type = (origins.push ty)[i]!
    rw [Array.getElem!_eq_getD] at htype ⊢
    unfold Array.getD at htype ⊢
    rw [dif_pos hiOrigins] at htype
    have hiPush : i < (origins.push ty).size := by
      simp only [Array.size_push]
      omega
    rw [dif_pos hiPush]
    have heq : (origins.push ty)[i]'hiPush = origins[i]'hiOrigins :=
      Array.getElem_push_lt hiOrigins
    exact htype.trans heq.symm

/-- Variant of `FVarArrayBinderTypes.pushCurrent` for a binder opened in both contexts. -/
def FVarArrayBinderTypes.pushCurrentChecked
    {base : LocalContext}
    (H : FVarArrayBinderTypes c xs origins)
    (Hc : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FVarArrayBinderTypes
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
        checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) (origins.push ty) := by
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withCheckedLocalDecl (base := base) c Hc name ty bi
  refine {
    bound := H.bound.pushCurrentChecked (base := base) name ty bi
    size_eq := by simpa using H.size_eq
    declaration := ?_ }
  intro i hi
  by_cases hilast : i = xs.size
  · subst i
    let D : FVarDeclAt c'
        (xs.push (.fvar ⟨c.ngen.curr⟩)) xs.size := {
      inBounds := by simp
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    refine ⟨D, ?_⟩
    change ty = (origins.push ty)[xs.size]!
    rw [show xs.size = origins.size from H.size_eq.symm]
    simp
  · have hiOld : i < xs.size := by
      have : i < xs.size + 1 := by simpa using hi
      omega
    rcases H.declaration i hiOld with ⟨D, htype⟩
    refine ⟨(D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep, ?_⟩
    have hsizes := H.size_eq
    have hiOrigins : i < origins.size := by omega
    change D.type = (origins.push ty)[i]!
    rw [Array.getElem!_eq_getD] at htype ⊢
    unfold Array.getD at htype ⊢
    rw [dif_pos hiOrigins] at htype
    have hiPush : i < (origins.push ty).size := by
      simp only [Array.size_push]
      omega
    rw [dif_pos hiPush]
    have heq : (origins.push ty)[i]'hiPush = origins[i]'hiOrigins :=
      Array.getElem_push_lt hiOrigins
    exact htype.trans heq.symm

theorem FVarArrayIn.getElem_eq_fvar
    (H : FVarArrayIn c xs) (i : Nat) (hi : i < xs.size) :
    ∃ hiFvars : i < H.fvars.length,
      xs[i] = .fvar H.fvars[i] := by
  rcases H with ⟨fvars, rfl, members⟩
  refine ⟨by simpa using hi, by simp⟩

/-- A selected free-variable array occupying a known slice of a larger
binder list translates, after simultaneous abstraction, to the corresponding
de Bruijn slice. -/
theorem FVarArrayIn.abstractedTranslationAt
    (H : FVarArrayIn c xs)
    (binders before after : List FVarId)
    (hsplit : binders = before ++ H.fvars ++ after)
    (hnodup : binders.Nodup)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((xs.map fun arg => arg.abstractList binders).toList)
      (List.ofFn fun i : Fin xs.size =>
        VExpr.bvar (binders.length - 1 - (before.length + i))) := by
  subst binders
  apply List.forall₂_of_getElem (by simp)
  intro i hsource htarget
  have hi : i < xs.size := by simpa using hsource
  rcases H.getElem_eq_fvar i hi with ⟨hiFvars, harg⟩
  have hposition : before.length + i <
      (before ++ H.fvars ++ after).length := by
    simp only [List.length_append]
    omega
  have hselected :
      (before ++ H.fvars ++ after)[before.length + i] = H.fvars[i] := by
    simp [hiFvars]
  have habstract := Expr.abstractList_fvar_getElem hnodup
    (before.length + i) hposition (k := 0)
  rw [hselected] at habstract
  simp only [Array.getElem_toList, Array.getElem_map,
    List.getElem_ofFn]
  rw [harg, habstract]
  have hbound :
      (before ++ H.fvars ++ after).length - 1 - (before.length + i) <
        domains.length := by
    rw [hdomains]
    omega
  simpa using TrExprS.bvar_of_abstractForallContext
    (env := env) (Us := Us) domains Δ
    ((before ++ H.fvars ++ after).length - 1 - (before.length + i))
    hbound

theorem FVarArrayIn.length_fvars
    (H : FVarArrayIn c xs) : H.fvars.length = xs.size := by
  have := congrArg Array.size H.expressions
  simpa using this.symm

theorem FVarArrayIn.get_fvars_sublist
    (H : FVarArrayIn c xs) (i : Nat) (hi : i < xs.size) :
    (H.get i hi).fvars <+ H.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  simp [FVarArrayIn.get, List.getElem_mem]

theorem FVarArrayIn.fvars_eq
    (H₁ : FVarArrayIn c xs) (H₂ : FVarArrayIn c ys)
    (hxy : xs = ys) : H₁.fvars = H₂.fvars := by
  have harr : (H₁.fvars.map Expr.fvar).toArray =
      (H₂.fvars.map Expr.fvar).toArray := by
    rw [← H₁.expressions, ← H₂.expressions, hxy]
  have hlist : H₁.fvars.map Expr.fvar = H₂.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harr
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist

/-- Binder identity is determined by the represented expression array, even
when the two `FVarArrayIn` facts are indexed by different contexts. -/
theorem FVarArrayIn.fvars_eq_of_array_eq
    (H₁ : FVarArrayIn c₁ xs) (H₂ : FVarArrayIn c₂ ys)
    (hxy : xs = ys) : H₁.fvars = H₂.fvars := by
  have harr : (H₁.fvars.map Expr.fvar).toArray =
      (H₂.fvars.map Expr.fvar).toArray := by
    rw [← H₁.expressions, ← H₂.expressions, hxy]
  have hlist : H₁.fvars.map Expr.fvar = H₂.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harr
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist

/-- Ordered selection of one bound-fvar array from another implies the
corresponding inclusion of free-variable identifiers. -/
theorem FVarArrayIn.fvars_subset_of_sublist
    (H₁ : FVarArrayIn c xs) (H₂ : FVarArrayIn c ys)
    (hxy : xs.toList.Sublist ys.toList) : H₁.fvars ⊆ H₂.fvars := by
  intro fv hfv
  have hx : Expr.fvar fv ∈ xs.toList := by
    rw [H₁.expressions]
    simpa using hfv
  have hy : Expr.fvar fv ∈ ys.toList := hxy.subset hx
  rw [H₂.expressions] at hy
  simpa using hy

/-- Any ordered subarray of a free-variable array is itself a
free-variable array.  The selected identifier list is recovered
from the `List.Sublist` derivation, so this does not assume an auxiliary
index map or re-run the executable classifier. -/
theorem FVarArrayIn.ofSublist
    (H : FVarArrayIn c ys) (hxy : xs.toList.Sublist ys.toList) :
    Nonempty (FVarArrayIn c xs) := by
  have extract : ∀ {es : List Expr} {fvars : List FVarId},
      es.Sublist (fvars.map Expr.fvar) →
      ∃ selected : List FVarId,
        es = selected.map Expr.fvar ∧ selected.Sublist fvars := by
    intro es fvars
    induction fvars generalizing es with
    | nil =>
      intro h
      have hes : es = [] := List.sublist_nil.mp (by simpa using h)
      subst es
      exact ⟨[], rfl, .slnil⟩
    | cons fv fvars ih =>
      intro h
      cases h with
      | cons _ htail =>
        rcases ih htail with ⟨selected, hes, hselected⟩
        exact ⟨selected, hes, .cons _ hselected⟩
      | cons_cons _ htail =>
        rcases ih htail with ⟨selected, hes, hselected⟩
        exact ⟨fv :: selected, by simp [hes], .cons_cons _ hselected⟩
  have hy : ys.toList = H.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList H.expressions
  have hsource : xs.toList.Sublist (H.fvars.map Expr.fvar) := by
    rwa [← hy]
  rcases extract hsource with ⟨selected, hselectedExprs, hselected⟩
  exact ⟨{
    fvars := selected
    expressions := by
      apply Array.toList_inj.mp
      simpa using hselectedExprs
    members := fun fv hfv =>
      H.members fv (hselected.subset hfv) }⟩

theorem FVarArrayIn.exprArrayFVarIds
    (H : FVarArrayIn c xs) : ExprArrayFVarIds xs = H.fvars := by
  calc
    ExprArrayFVarIds xs =
        ExprArrayFVarIds ((H.fvars.map Expr.fvar).toArray) :=
      congrArg ExprArrayFVarIds H.expressions
    _ = H.fvars := by
      simp [ExprArrayFVarIds, recursorFVarId, Function.comp_def]

/-- All local free-variable arrays stored in the executable recursor-info
records, aligned with the executable array operations. -/
structure RecInfoBindings (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) where
  motives : FVarArrayIn c (recInfos.map (·.motive))
  majors : FVarArrayIn c (recInfos.map (·.major))
  indices : ∀ i (_hi : i < recInfos.size),
    FVarArrayIn c recInfos[i]!.indices
  minors : ∀ i (_hi : i < recInfos.size),
    FVarArrayIn c recInfos[i]!.minors

/-- The constructor traversal which produced one minor.  It is optional in
`MinorPremiseType.traversal`; the source alignment `MinorsMatchConstructors`
requires it to be present. -/
structure ConstructorFieldTraversal where
  constructor : Constructor
  rootContext : AddInductive.Context
  terminalContext : AddInductive.Context
  terminal : Expr
  fields : Array Expr
  recursiveFields : Array Expr
  stats : AddInductive.InductiveStats
  recursivePositions : List Nat
  recursivePositions_ordered : recursivePositions.Pairwise (· < ·)
  recursivePositions_lt : ∀ position ∈ recursivePositions,
    position < fields.size
  recursivePositions_length : recursivePositions.length = recursiveFields.size
  parameterTail : Expr
  parameterTail_fvars : parameterTail.FVarsIn (· ∈ rootContext.lctx.fvars)
  decisions : RecursorFieldDecisions stats rootContext parameterTail
    terminalContext terminal fields recursiveFields recursivePositions
  parameterPrefix : ParameterPrefix stats 0 constructor.type parameterTail
  fieldFVars : List FVarId
  fields_eq : fields = (fieldFVars.map Expr.fvar).toArray
  fieldFVars_nodup : fieldFVars.Nodup
  fieldResidual : Expr
  fieldTelescope : Expr.ForallTelescope parameterTail fields.size fieldResidual
  fieldClosed : terminal.abstractList fieldFVars = fieldResidual
  fieldResidual_not_forall : fieldResidual.isForall = false

/-- Alpha-invariant source construction of one induction-hypothesis
declaration.  This compact form is stored with the generated minor after the
executable `loopU` accumulator has gone out of scope. -/
structure InductionHypothesisShape where
  ownerIdx : Nat
  localArity : Nat
  localTelescope : Expr
  motive : Expr
  indices : Array Expr

/-- The checker context in which `loopUArgs` normalizes the type of a
recursive field: the main context restricted to `prior`, the parameters and
the fields before it. -/
def loopUArgsCheckLCtx (c : AddInductive.Context) (prior : Array Expr) :
    LocalContext :=
  c.lctx.restrictTo (prior.toList.map (·.fvarId!))

theorem List.takeWhile_fvarId_prefix (fv : FVarId) :
    ∀ (l : List Expr), (∃ x ∈ l, x.fvarId! = fv) →
      (l.takeWhile (·.fvarId! != fv)).map (·.fvarId!) =
        (l.map (·.fvarId!)).take (l.takeWhile (·.fvarId! != fv)).length ∧
      (l.map (·.fvarId!))[(l.takeWhile (·.fvarId! != fv)).length]? = some fv
  | [], ⟨_, h, _⟩ => by simp at h
  | x :: xs, hmem => by
    by_cases hx : x.fvarId! = fv
    · simp [hx]
    · obtain ⟨y, hy, hyfv⟩ := hmem
      have hy' : ∃ y ∈ xs, y.fvarId! = fv := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hyfv hx
        · exact ⟨y, hy, hyfv⟩
      obtain ⟨h1, h2⟩ := List.takeWhile_fvarId_prefix fv xs hy'
      have hp : (x.fvarId! != fv) = true := by simpa using hx
      simp only [List.takeWhile_cons, hp, ↓reduceIte, List.map_cons,
        List.length_cons, List.take_succ_cons, List.getElem?_cons_succ]
      exact ⟨congrArg _ h1, h2⟩

/-- The checker entries before a recursive field: the parameters and the
fields before it, as a prefix of the parameters and all fields. -/
theorem fieldsBefore_priorFVars (stats : AddInductive.InductiveStats)
    (bu : Array Expr) (fv : FVarId) (hmem : ∃ x ∈ bu.toList, x.fvarId! = fv) :
    ∃ k, (AddInductive.mkRecInfos.fieldsBefore stats bu (.fvar fv)).toList.map
        (·.fvarId!) = ((stats.params ++ bu).toList.map (·.fvarId!)).take k ∧
      ((stats.params ++ bu).toList.map (·.fvarId!))[k]? =
        some (Expr.fvar fv).fvarId! := by
  obtain ⟨h1, h2⟩ := List.takeWhile_fvarId_prefix fv bu.toList hmem
  refine ⟨(stats.params.toList.map (·.fvarId!)).length +
    (bu.toList.takeWhile (·.fvarId! != fv)).length, ?_, ?_⟩
  · change (stats.params ++ bu.takeWhile (fun x => x.fvarId! != fv)).toList.map
      (·.fvarId!) = _
    rw [Array.toList_append, Array.toList_takeWhile, List.map_append,
      Array.toList_append, List.map_append, List.take_length_add_append, h1]
  · rw [Array.toList_append, List.map_append,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact h2

/-- The executable input of one `loopUArgs` traversal: the field's inferred
type and its `whnf` in the checker context of the earlier fields.  Recording
both runs fixes the normalized field domain the traversal starts from. -/
structure LoopUArgsInput
    (root : AddInductive.Context) (field : Expr) where
  /-- The parameters and the fields before `field`: the checker entries
  before it. -/
  prior : Array Expr
  priorFVars : ∃ k, prior.toList.map (·.fvarId!) =
      ((root.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
    ((root.checkLCtx.toList.map (·.fvarId)).reverse)[k]? = some field.fvarId!
  inferredType : Expr
  normalizedType : Expr
  inference : AddInductive.getType field root = .ok inferredType
  normalization :
    (monadLift (TypeChecker.whnf inferredType) : AddInductive.M Expr)
      { root with checkLCtx := loopUArgsCheckLCtx root prior } =
      .ok normalizedType

/-- The checker context of a `loopUArgs` run over `prior`, rebuilt in any
recursor frame of its root: the checker entries before the field, among which
the field's declared type is translated. -/
theorem RecursorContextWF.priorBase
    {root : AddInductive.Context} {fv : FVarId} {prior : Array Expr}
    {recLparams : List Name} (R : RecursorContextWF root recLparams)
    (hpriorFVars : ∃ k, prior.toList.map (·.fvarId!) =
        ((root.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
      ((root.checkLCtx.toList.map (·.fvarId)).reverse)[k]? =
        some (Expr.fvar fv).fvarId!) :
    ∃ (j : Nat) (hj : j ≤ R.chk.length) (ty₀ : VExpr),
      (R.chk.dropN j hj).lctx = loopUArgsCheckLCtx root prior ∧
      TrExprS R.venv recLparams (R.chk.dropN j hj).vlctx
        (root.lctx.get! fv).type ty₀ ∧
      R.venv.IsType recLparams.length (R.chk.dropN j hj).vlctx.toCtx ty₀ ∧
      ∃ k, (R.chk.dropN j hj).fvarList = R.chk.fvarList.take k ∧
        R.chk.fvarList[k]? = some fv := by
  obtain ⟨k, hprior, hk⟩ := hpriorFVars
  have hlist : (root.checkLCtx.toList.map (·.fvarId)).reverse = R.chk.fvarList := by
    rw [← R.check.lctx_eq, R.check.wf.toList_eq, TypeChecker.MLCtx.decls_fvarId,
      List.reverse_reverse]
  rw [hlist] at hprior hk
  obtain ⟨j, hj, name, ty, ty', bi, hdrop, htake⟩ :=
    R.chk.dropN_of_fvarList_getElem? R.check.onlyLams hk
  have hw := R.check.wf.dropN j (Nat.le_of_succ_le hj)
  rw [hdrop] at hw
  obtain ⟨_, _, htr, hty⟩ := hw
  -- the field's declared type, read off the main context
  have hmem : fv ∈ (R.chk.dropN j (Nat.le_of_succ_le hj)).vlctx.fvars := by
    rw [hdrop]; simp [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, Expr.fvarId!]
  have hfind := R.check.onlyLams.dropN_find?_eq R.check.wf j _ hmem
  rw [hdrop] at hfind
  have hfind' : R.chk.lctx.find? fv = some (.cdecl
      (R.chk.dropN (j + 1) hj).lctx.decls.size fv name ty bi .default) := by
    rw [hfind]
    change ((R.chk.dropN (j + 1) hj).lctx.mkLocalDecl fv name ty bi).find? fv = _
    rw [LocalContext.find?_mkLocalDecl
      (R.check.wf.dropN (j + 1) hj).tr.1.map_wf]
    simp
  rw [R.check.lctx_eq] at hfind'
  obtain ⟨d', hd', hdeq⟩ := R.check.sub fv _ hfind'
  have htype : (root.lctx.get! fv).type = ty := by
    have e1 : ∀ x : LocalDecl, (x.setIndex 0).type = x.type := by
      intro x; cases x <;> rfl
    simp only [LocalContext.get!, hd']
    rw [← e1 d', hdeq]
    rfl
  refine ⟨j + 1, hj, ty', ?_, htype ▸ htr, hty, k, htake.symm, hk⟩
  rw [loopUArgsCheckLCtx, hprior, htake]
  exact ((R.check.below (j + 1) hj).restrictTo_eq).symm

theorem LoopUArgsInput.checkBase
    {root : AddInductive.Context} {fv : FVarId}
    (H : LoopUArgsInput root (.fvar fv))
    {recLparams : List Name} (R : RecursorContextWF root recLparams) :
    ∃ (j : Nat) (hj : j ≤ R.chk.length) (ty₀ : VExpr),
      (R.chk.dropN j hj).lctx = loopUArgsCheckLCtx root H.prior ∧
      TrExprS R.venv recLparams (R.chk.dropN j hj).vlctx
        (root.lctx.get! fv).type ty₀ ∧
      R.venv.IsType recLparams.length (R.chk.dropN j hj).vlctx.toCtx ty₀ ∧
      ∃ k, (R.chk.dropN j hj).fvarList = R.chk.fvarList.take k ∧
        R.chk.fvarList[k]? = some fv :=
  R.priorBase H.priorFVars

/-- Successful prefix of the executable `loopUArgs.loop` traversal.
This ties the terminal expression,
fresh argument array, and terminal context to the normalized input
and every intervening `whnf` call. -/
inductive LoopUArgsRun
    (root : AddInductive.Context) (l : LocalContext) (source : Expr) :
    AddInductive.Context → Expr → Array Expr → Prop
  | root : LoopUArgsRun root l source { root with checkLCtx := l } source #[]
  | push
      {current next : AddInductive.Context} {args : Array Expr}
      {name : Name} {domain body normalized : Expr} {bi : BinderInfo}
      (previous : LoopUArgsRun root l source current
        (.forallE name domain body bi) args)
      (next_eq : next = { current with
        ngen := current.ngen.next
        lctx := current.lctx.mkLocalDecl ⟨current.ngen.curr⟩ name
          (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi
        checkLCtx := current.checkLCtx.mkLocalDecl ⟨current.ngen.curr⟩ name
          (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi })
      (normalization :
        (monadLift (TypeChecker.whnf
          (body.instantiate1 (.fvar ⟨current.ngen.curr⟩))) :
            AddInductive.M Expr) next = .ok normalized) :
      LoopUArgsRun root l source next normalized
        (args.push (.fvar ⟨current.ngen.curr⟩))

/-- A run rooted at a checker-context variant of `root` is rooted at
`root`: the root's checker context plays no role. -/
theorem LoopUArgsRun.ofCheckRoot {root : AddInductive.Context}
    {l l' : LocalContext} {source : Expr} {current : AddInductive.Context}
    {exposed : Expr} {args : Array Expr}
    (H : LoopUArgsRun { root with checkLCtx := l' } l source current
      exposed args) :
    LoopUArgsRun root l source current exposed args := by
  induction H with
  | root => exact .root
  | push _ next_eq normalization ih => exact .push ih next_eq normalization

end VerifyInductive
end Lean4Lean
