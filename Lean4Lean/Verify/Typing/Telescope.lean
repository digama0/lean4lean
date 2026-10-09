import Lean4Lean.Verify.Expr.Telescope
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.VExpr.TelescopeLemmas

/-! Generic translations of forall and lambda telescopes. Anonymous contexts
use outermost-to-innermost domain order; translation, domain typing, residual
translation, and context conversion remain separate explicit obligations.
Inductive phase certificates and executable checking scopes live in the adapter.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

attribute [simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj


/-- `Expr.inferImplicit` changes only binder annotations, which the translation erases.
In particular the abstract recursor type proved for the generated type is still the
translation of the type after `inferImplicit`, which is the one installed. -/
theorem TrExprS.inferImplicit
    (H : TrExprS env Us Δ e e') (numParams : Nat) (considerRange : Bool) :
    TrExprS env Us Δ (e.inferImplicit numParams considerRange) e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        simp only [Expr.inferImplicit]
        exact .forallE hdomType hbodyType hdom
          (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- Conversely, `inferImplicit` can be removed from the executable side of a
translation. -/
theorem TrExprS.of_inferImplicit
    (H : TrExprS env Us Δ (e.inferImplicit numParams considerRange) e') :
    TrExprS env Us Δ e e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        exact .forallE hdomType hbodyType hdom (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H


/-- Translation erases names and binder annotations but preserves the exact
number of leading forall binders. -/
theorem TrExprS.forallTelescope_shape
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' := by
  induction Htel generalizing Δ e' with
  | nil => exact ⟨[], e', rfl, rfl⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq⟩
      exact ⟨ty' :: domains, result', by simp [hlength], by
        simp [VExpr.wrapForalls, heq]⟩

def abstractForallContext (domains : List VExpr) (Δ : VLCtx) : VLCtx :=
  (domains.reverse.map fun type => (none, .vlam type)) ++ Δ

@[simp] theorem VLCtx.instL_append
    (left right : VLCtx) (levels : List VLevel) :
    (left ++ right).instL levels =
      left.instL levels ++ right.instL levels := by
  induction left with
  | nil => rfl
  | cons entry left ih =>
    rcases entry with ⟨ofv, decl⟩
    simp [VLCtx.instL, ih]

@[simp] theorem VLCtx.instL_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (levels : List VLevel) :
    (abstractForallContext domains Δ).instL levels =
      abstractForallContext (domains.map (VExpr.instL levels))
        (Δ.instL levels) := by
  have hmap : ∀ types : List VExpr,
      VLCtx.instL
          (types.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) levels =
      types.map fun type =>
        ((none, .vlam (type.instL levels)) :
          Option (FVarId × List FVarId) × VLocalDecl) := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih =>
      simp [VLCtx.instL, VLocalDecl.instL, ih]
  unfold abstractForallContext
  rw [VLCtx.instL_append]
  rw [← List.map_reverse]
  rw [hmap domains.reverse]
  simp [List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem abstractForallContext_toCtx
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).toCtx =
      domains.reverse ++ Δ.toCtx := by
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  unfold abstractForallContext
  rw [VLCtx.toCtx_append, htoCtx domains.reverse]

theorem _root_.Lean4Lean.OnCtx.drop (H : OnCtx Γ P) (n : Nat) :
    OnCtx (Γ.drop n) P := by
  induction n generalizing Γ with
  | zero => exact H
  | succ n ih =>
    cases Γ with
    | nil => exact H
    | cons head tail => exact ih H.1

@[simp] theorem abstractForallContext_fvars
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).fvars = Δ.fvars := by
  rw [abstractForallContext, VLCtx.fvars_append]
  have hnone : VLCtx.fvars
      (domains.reverse.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = [] := by
    let types := domains.reverse
    change VLCtx.fvars
      (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = []
    induction types with
    | nil => rfl
    | cons type types ih =>
      simp only [List.map_cons, VLCtx.fvars_cons_none, ih]
  rw [hnone, List.nil_append]

@[simp] theorem abstractForallContext_bvars
    (domains : List VExpr) (Δ : VLCtx) :
    (abstractForallContext domains Δ).bvars =
      domains.length + Δ.bvars := by
  simp only [abstractForallContext, VLCtx.bvars_append]
  have hmap : ∀ types : List VExpr,
      VLCtx.bvars (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types.length := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.bvars, ih]
  rw [hmap]
  simp

/-- Extend a converted outer context by the same well-formed dependent inner
prefix on both sides. -/
theorem VEnv.IsDefEqCtx.extendSamePrefix
    (H : VEnv.IsDefEqCtx env U [] left right)
    (Hctx : OnCtx (types ++ left) (env.IsType U)) :
    VEnv.IsDefEqCtx env U [] (types ++ left) (types ++ right) := by
  induction types with
  | nil => simpa using H
  | cons type types ih =>
    rcases Hctx with ⟨Htail, level, Htype⟩
    exact .succ (ih Htail) Htype

/-- Context-conversion wrapper in outermost-to-innermost domain order. -/
theorem abstractForallContext.isDefEq
    (H : VEnv.IsDefEqCtx env U [] left.reverse right.reverse) :
    VLCtx.IsDefEq env U
      (abstractForallContext left [])
      (abstractForallContext right []) := by
  simpa [abstractForallContext] using
    VLCtx.IsDefEq.ofDefEqCtxAnonymous H

/-- Translation uniqueness over two independently assembled anonymous
dependent contexts, stated in the plain-context conversion form that the telescope
lemmas produce. -/
theorem TrExprS.uniqAbstractForallContext
    {domainsLeft domainsRight : List VExpr}
    (Hleft : TrExprS env Us (abstractForallContext domainsLeft []) source
      leftTarget)
    (Hright : TrExprS env Us (abstractForallContext domainsRight []) source
      rightTarget)
    (henv : VEnv.WF env)
    (Hctx : VEnv.IsDefEqCtx env Us.length [] domainsLeft.reverse
      domainsRight.reverse) :
    env.IsDefEqU Us.length domainsLeft.reverse leftTarget rightTarget := by
  have Hvlctx := abstractForallContext.isDefEq Hctx
  have Huniq := Hleft.uniq henv Hvlctx Hright
  simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Huniq

/-- Anonymous lambda contexts of equal length have the same lookup shape.
This is the structural premise needed to recover the exact target of a
syntax-directed translation after context conversion. -/
theorem TrExprS.IsUniqueCtx.anonymousLams
    {left right : List VExpr}
    (hlen : left.length = right.length) :
    TrExprS.IsUniqueCtx
      (left.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl))
      (right.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) := by
  induction left generalizing right with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    exact .base
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      exact .cons (ih (Nat.succ.inj hlen)) .vlam

/-- Outermost-to-innermost anonymous forall contexts retain unique lookup
shape whenever their telescope lengths agree. -/
theorem abstractForallContext.isUniqueCtx
    {left right : List VExpr}
    (hlen : left.length = right.length) :
    TrExprS.IsUniqueCtx
      (abstractForallContext left [])
      (abstractForallContext right []) := by
  simpa [abstractForallContext] using
    (TrExprS.IsUniqueCtx.anonymousLams
      (left := left.reverse) (right := right.reverse) (by simp [hlen]))

/-- Locate the first retained free-variable declaration below an anonymous
forall prefix and replace it by the corresponding bound-variable declaration.
The source and target contexts have definitionally identical typing lists;
only the source-variable lookup changes. -/
theorem abstractForallContext.abstractHead
    (domains : List VExpr) (tail : VLCtx) (fv : FVarId)
    (deps : List FVarId) (type : VExpr) :
    VLCtx.Abstract tail fv (.vlam type) domains.length domains.length
      (abstractForallContext domains
        ((some (fv, deps), .vlam type) :: tail))
      (abstractForallContext (type :: domains) tail) := by
  have go : ∀ pre : List VExpr,
      VLCtx.Abstract tail fv (.vlam type) pre.length pre.length
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          (some (fv, deps), .vlam type) :: tail)
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          (none, .vlam type) :: tail) := by
    intro pre
    induction pre with
    | nil => exact .zero
    | cons domain pre ih =>
      simpa [VLocalDecl.depth, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using VLCtx.Abstract.succ
          (d := .vlam domain) ih
  simpa [abstractForallContext, List.reverse_cons, List.map_append,
    List.append_assoc] using go domains.reverse

/-- Abstract a reverse-ordered prefix of free-variable lambda declarations
while retaining an arbitrary older context tail.  The closed declarations
become anonymous domains outside the already present `domains`; the tail is
left untouched. -/
theorem TrExprS.abstractFVarLambdaPrefix
    (Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvsRev scopePrefix)
    (hnodup : fvsRev.Nodup)
    (Htr : TrExprS env Us
      (abstractForallContext domains (scopePrefix ++ tail)) e e') :
    TrExprS env Us
      (abstractForallContext
        ((VLCtx.toCtx scopePrefix).reverse ++ domains) tail)
      (e.abstractList fvsRev.reverse domains.length) e' := by
  induction Hdecls generalizing domains e with
  | nil => simpa [VLCtx.toCtx] using Htr
  | @cons fv entry fvsRev scopePrefix hentry Hrest ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    have hnodup' := List.nodup_cons.mp hnodup
    have W := abstractForallContext.abstractHead
      domains (scopePrefix ++ tail) fv deps type
    have Hhead := Htr.abstract W
    have hfv : fv ∉ fvsRev.reverse := by
      simpa using hnodup'.1
    have Htail := ih hnodup'.2 Hhead
    have hsource :
        (e.abstract1 fv domains.length).abstractList fvsRev.reverse
            (type :: domains).length =
          e.abstractList (fv :: fvsRev).reverse domains.length := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := e) (a := fv) (as := fvsRev.reverse)
        (k := domains.length) hfv).symm
    rw [hsource] at Htail
    simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using Htail


/-- Abstract a reverse-ordered suffix of free-variable lambda declarations
under an existing anonymous prefix.  The declaration order is newest first,
so successive abstractions occur at increasing cutoffs; the resulting source
is the ordinary simultaneous abstraction in oldest-first binder order. -/
theorem TrExprS.abstractFVarLambdaSuffix
    (Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      fvsRev scope)
    (hnodup : fvsRev.Nodup)
    (Htr : TrExprS env Us (abstractForallContext domains scope) e e') :
    TrExprS env Us
      (abstractForallContext ((VLCtx.toCtx scope).reverse ++ domains) [])
      (e.abstractList fvsRev.reverse domains.length) e' := by
  induction Hdecls generalizing domains e with
  | nil => simpa [VLCtx.toCtx] using Htr
  | @cons fv entry fvsRev scope hentry Htail ih =>
    rcases hentry with ⟨deps, type, rfl⟩
    have hnodup' := List.nodup_cons.mp hnodup
    have W := abstractForallContext.abstractHead
      domains scope fv deps type
    have Hhead := Htr.abstract W
    have hfv : fv ∉ fvsRev.reverse := by
      simpa using hnodup'.1
    have Hrest := ih hnodup'.2 Hhead
    have hsource :
        (e.abstract1 fv domains.length).abstractList fvsRev.reverse
            (type :: domains).length =
          e.abstractList (fv :: fvsRev).reverse domains.length := by
      rw [List.reverse_cons, Expr.abstractList_append]
      simp only [Expr.abstractList]
      simpa using (Expr.abstract1_abstractList
        (e := e) (a := fv) (as := fvsRev.reverse)
        (k := domains.length) hfv).symm
    rw [hsource] at Hrest
    simpa [VLCtx.toCtx, List.reverse_cons, List.append_assoc] using Hrest


/-- Abstracting an outer binder list after an already abstracted inner list
at the inner-list cutoff is equivalent to their ordinary outer-to-inner
simultaneous abstraction. -/
theorem Expr.abstractList_after_inner
    {e : Expr} {outer inner : List FVarId} {k : Nat}
    (hnodup : (outer ++ inner).Nodup) :
    (e.abstractList inner k).abstractList outer (k + inner.length) =
      e.abstractList (outer ++ inner) k := by
  induction outer generalizing e with
  | nil => simp
  | cons fv outer ih =>
    have hnodup' := List.nodup_cons.mp hnodup
    have hfvInner : fv ∉ inner := by
      exact fun h => hnodup'.1 (List.mem_append_right outer h)
    have htail : (outer ++ inner).Nodup := by
      simpa [List.cons_append] using hnodup'.2
    have hfvInnerNodup : (fv :: inner).Nodup :=
      List.nodup_cons.mpr ⟨hfvInner, (List.nodup_append.mp htail).2.1⟩
    simp only [List.cons_append, Expr.abstractList]
    rw [Expr.abstract1_abstractList'
      (e := e) (a := fv) (as := inner) (k := k)
      hfvInnerNodup]
    exact ih htail

/-- Exact-model form of `abstractList_after_inner`; no distinctness is needed, since the
last occurrence of a variable wins in both the combined and the two-step abstraction. -/
theorem Expr.abstractN_after_inner {e : Expr} {outer inner : List FVarId} {k : Nat} :
    (e.abstractN inner k).abstractN outer (k + inner.length) =
      e.abstractN (outer ++ inner) k :=
  (Expr.abstractN_append outer inner e k).symm

/-- If abstraction has no unexpected free variables, the original expression
can only additionally mention the variable that was abstracted. -/
theorem FVarsIn.of_abstract1
    {e : Expr} {fv : FVarId} {k : Nat} {P : FVarId → Prop}
    (H : (e.abstract1 fv k).FVarsIn P) :
    e.FVarsIn fun other => other = fv ∨ P other := by
  induction e generalizing k with
  | bvar i => trivial
  | fvar other =>
    by_cases h : other = fv
    · simp [h, FVarsIn]
    · simpa [FVarsIn, Expr.abstract1, h, Ne.symm h] using H
  | sort level => simpa [FVarsIn, Expr.abstract1] using H
  | const name levels => simpa [FVarsIn, Expr.abstract1] using H
  | mvar id => simp [FVarsIn, Expr.abstract1] at H
  | lit literal => trivial
  | app fn arg ihFn ihArg =>
    exact ⟨ihFn H.1, ihArg H.2⟩
  | lam name type body bi ihType ihBody =>
    exact ⟨ihType H.1, ihBody H.2⟩
  | forallE name type body bi ihType ihBody =>
    exact ⟨ihType H.1, ihBody H.2⟩
  | letE name type value body bi ihType ihValue ihBody =>
    exact ⟨ihType H.1, ihValue H.2.1, ihBody H.2.2⟩
  | mdata data body ih => exact ih H
  | proj name index body ih => exact ih H

/-- List form of `FVarsIn.of_abstract1`. -/
theorem FVarsIn.of_abstractList
    {e : Expr} {fvars : List FVarId} {k : Nat} {P : FVarId → Prop}
    (H : (e.abstractList fvars k).FVarsIn P) :
    e.FVarsIn fun fv => fv ∈ fvars ∨ P fv := by
  induction fvars generalizing e with
  | nil => simpa using H
  | cons fv fvars ih =>
    have Htail := ih H
    have Hhead := FVarsIn.of_abstract1 Htail
    exact Hhead.mono fun other h => by
      rcases h with h | h
      · simp [h]
      · rcases h with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

@[simp] theorem abstractForallContext_append
    (outer inner : List VExpr) (Δ : VLCtx) :
    abstractForallContext inner (abstractForallContext outer Δ) =
      abstractForallContext (outer ++ inner) Δ := by
  simp [abstractForallContext, List.reverse_append, List.map_append,
    List.append_assoc]

/-- Prepending the abstract lambda domains is the canonical bound-variable
lift of the retained outer context. -/
theorem abstractForallContext.bvLift
    (domains : List VExpr) (Δ : VLCtx) :
    VLCtx.BVLift Δ (abstractForallContext domains Δ)
      domains.length 0 domains.length 0 := by
  have hprefix : ∀ (pref : List VExpr),
      VLCtx.BVLift Δ
        ((pref.map fun type => (none, .vlam type)) ++ Δ)
        pref.length 0 pref.length 0 := by
    intro pref
    induction pref with
    | nil => exact .refl
    | cons type pref ih =>
      simpa [VLocalDecl.depth, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        VLCtx.BVLift.skip (.vlam type) ih
  simpa [abstractForallContext] using hprefix domains.reverse

/-- Insert a block between an outer telescope and an existing inner prefix.
The dependent inner domains are lifted exactly as `Ctx.LiftN` requires, while
the source and target binder counts expose the cutoff used on residuals. -/
theorem abstractForallContext.bvInsertBeforeInner
    (outer inserted inner : List VExpr) :
    let liftedInner :=
      (liftContextPrefix inserted.length inner.reverse).reverse
    VLCtx.BVLift
      (abstractForallContext (outer ++ inner) [])
      (abstractForallContext (outer ++ inserted ++ liftedInner) [])
      inserted.length inner.length inserted.length inner.length := by
  let outerCtx := abstractForallContext outer []
  have go : ∀ pre : List VExpr,
      VLCtx.BVLift
        ((pre.map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++ outerCtx)
        (((liftContextPrefix inserted.length pre).map fun domain =>
            ((none, .vlam domain) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++
          abstractForallContext inserted outerCtx)
        inserted.length pre.length inserted.length pre.length := by
    intro pre
    induction pre with
    | nil =>
      simpa [liftContextPrefix, liftContextPrefixAt, outerCtx] using
        abstractForallContext.bvLift inserted outerCtx
    | cons domain pre ih =>
      simpa [liftContextPrefix, liftContextPrefixAt, VLocalDecl.depth,
        VLocalDecl.liftN,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        VLCtx.BVLift.cons (.vlam domain) ih
  simpa [abstractForallContext, outerCtx, List.reverse_append,
    List.map_append, List.append_assoc] using go inner.reverse

/-- Translation-level form of `bvInsertBeforeInner`: insert a telescope
between already closed outer and inner binders, lifting both residuals at
the inner-binder cutoff. -/
theorem TrExprS.insertBeforeInner
    (henv : env.Ordered)
    (Htr : TrExprS env Us
      (abstractForallContext (outer ++ inner) []) source target)
    (inserted : List VExpr) :
    let liftedInner :=
      (liftContextPrefix inserted.length inner.reverse).reverse
    TrExprS env Us
      (abstractForallContext (outer ++ inserted ++ liftedInner) [])
      (source.liftLooseBVars' inner.length inserted.length)
      (target.liftN inserted.length inner.length) := by
  let W := abstractForallContext.bvInsertBeforeInner outer inserted inner
  simpa using Htr.weakBV henv W

/-- Telescope inversion that also records the abstract context in which the residual is
translated. -/
theorem TrExprS.forallTelescope_shape_with_context
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' ∧
      TrExprS env Us (abstractForallContext domains Δ) result result' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl, by simpa [abstractForallContext] using Htr⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq, hresult⟩
      refine ⟨ty' :: domains, result', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapForalls, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresult

/-- A nonempty translated concrete forall telescope is an abstract type.
The translation constructor already carries exactly the two typing premises
needed for abstract forall formation. -/
theorem TrExprS.isType_of_forallTelescope
    (Htel : Expr.ForallTelescope e arity result)
    (hpositive : 0 < arity)
    (Htr : TrExprS env Us Δ e e') :
    env.IsType Us.length Δ.toCtx e' := by
  cases Htel with
  | nil => omega
  | cons _ =>
    cases Htr with
    | forallE hdomType hbodyType _ _ =>
      exact VEnv.IsType.forallE hdomType hbodyType

/-- Compositional semantic certificate for a concrete forall telescope.
Unlike a bare whole-expression translation, this exposes the translation and
typehood obligation at every binder and at the final residual. -/
inductive Expr.ForallTelescopeTypeTranslation
    (env : VEnv) (Us : List Name) : VLCtx → Expr → Nat → VExpr → Prop
  | nil (Htr : TrExprS env Us Δ body body')
      (Htype : env.IsType Us.length Δ.toCtx body') :
      Expr.ForallTelescopeTypeTranslation env Us Δ body 0 body'
  | cons
      (Hdom : TrExprS env Us Δ dom dom')
      (HdomType : env.IsType Us.length Δ.toCtx dom')
      (Hbody : Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam dom') :: Δ) body n body') :
      Expr.ForallTelescopeTypeTranslation env Us Δ
        (.forallE name dom body bi) (n + 1) (.forallE dom' body')

theorem Expr.ForallTelescopeTypeTranslation.isType
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    env.IsType Us.length Δ.toCtx e' := by
  induction H with
  | nil _ Htype => exact Htype
  | cons _ HdomType _ ih => exact .forallE HdomType ih

theorem Expr.ForallTelescopeTypeTranslation.translation
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    TrExprS env Us Δ e e' := by
  induction H with
  | nil Htr _ => exact Htr
  | cons Hdom HdomType Hbody ih =>
    exact .forallE HdomType Hbody.isType Hdom ih

theorem Expr.ForallTelescopeTypeTranslation.mono
    (henv : env ≤ env')
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source arity target) :
    Expr.ForallTelescopeTypeTranslation env' Us Δ source arity target := by
  induction H with
  | nil Htr Htype => exact .nil (Htr.mono henv) (Htype.mono henv)
  | cons Hdom HdomType Hbody ih =>
    exact .cons (Hdom.mono henv) (HdomType.mono henv) ih

theorem Expr.ForallTelescopeTypeTranslation.telescope
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ e n e') :
    ∃ residual, Expr.ForallTelescope e n residual := by
  induction H with
  | nil => exact ⟨_, .nil _⟩
  | cons _ _ _ ih =>
    rcases ih with ⟨residual, Htel⟩
    exact ⟨residual, .cons Htel⟩

/-- Expose the abstract domains and residual carried by a binder-by-binder
translation.  The residual is typed in precisely the context obtained by
opening those domains, so callers can apply a term to the bvar spine of the binders
without reconstructing any domain syntax. -/
theorem Expr.ForallTelescopeTypeTranslation.toWrapForalls
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target) :
    ∃ domains sourceResidual targetResidual,
      domains.length = n ∧
      Expr.ForallTelescope source n sourceResidual ∧
      target = VExpr.wrapForalls domains targetResidual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        sourceResidual targetResidual ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx
        targetResidual := by
  induction H with
  | nil Htr Htype =>
    exact ⟨[], _, _, rfl, .nil _, rfl, by
      simpa [abstractForallContext] using Htr, by
      simpa [abstractForallContext] using Htype⟩
  | @cons Δ dom domTarget body n bodyTarget name bi
      Hdom HdomType Hbody ih =>
    rcases ih with
      ⟨domains, sourceResidual, targetResidual, hlength, Htelescope,
        htarget, Hresidual, HresidualType⟩
    refine ⟨domTarget :: domains, sourceResidual, targetResidual,
      by simp [hlength], .cons Htelescope, ?_, ?_, ?_⟩
    · simp [VExpr.wrapForalls, htarget]
    · simpa [abstractForallContext, List.map_append,
        List.append_assoc] using Hresidual
    · simpa [abstractForallContext, List.map_append,
        List.append_assoc] using HresidualType

/-- Split an exactly sized typed telescope after `prefixArity` binders,
retaining both the translated prefix domains and the binder-by-binder typed
suffix in the anonymous abstract context of the prefix. -/
theorem Expr.ForallTelescopeTypeTranslation.dropPrefix
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source
      (prefixArity + suffixArity) target) :
    ∃ prefixDomains suffixSource suffixTarget,
      prefixDomains.length = prefixArity ∧
      Expr.ForallTelescope source prefixArity suffixSource ∧
      target = VExpr.wrapForalls prefixDomains suffixTarget ∧
      Expr.ForallTelescopeTypeTranslation env Us
        (abstractForallContext prefixDomains Δ)
        suffixSource suffixArity suffixTarget := by
  induction prefixArity generalizing Δ source target with
  | zero =>
    exact ⟨[], source, target, rfl, .nil source, by rfl, by
      simpa [abstractForallContext] using H⟩
  | succ prefixArity ih =>
    rw [show (prefixArity + 1) + suffixArity =
      (prefixArity + suffixArity) + 1 by omega] at H
    cases H with
    | @cons Δ dom domTarget body arity bodyTarget name bi
        Hdom HdomType Hbody =>
      rcases ih Hbody with
        ⟨domains, suffixSource, suffixTarget, hlength, Hsource,
          htarget, Hsuffix⟩
      refine ⟨domTarget :: domains, suffixSource, suffixTarget,
        by simp [hlength], .cons Hsource, ?_, ?_⟩
      · simp [VExpr.wrapForalls, htarget]
      · simpa [abstractForallContext, List.map_append,
          List.append_assoc] using Hsuffix

/-- Select one binder from a typed translated telescope.  The returned
source domain is translated and typed in the exact abstract context formed
by the preceding target domains; the remaining body keeps its full
binder-by-binder certificate. -/
theorem Expr.ForallTelescopeTypeTranslation.binderAt
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target)
    (i : Nat) (hi : i < n) :
    ∃ prefixDomains suffixSource name sourceDomain sourceBody bi
        domainTarget bodyTarget,
      prefixDomains.length = i ∧
      Expr.ForallTelescope source i suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      target = VExpr.wrapForalls prefixDomains
        (.forallE domainTarget bodyTarget) ∧
      TrExprS env Us (abstractForallContext prefixDomains Δ)
        sourceDomain domainTarget ∧
      env.IsType Us.length
        (abstractForallContext prefixDomains Δ).toCtx domainTarget ∧
      Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam domainTarget) ::
          abstractForallContext prefixDomains Δ)
        sourceBody (n - i - 1) bodyTarget := by
  have hn : n = i + (n - i) := by omega
  rw [hn] at H
  rcases H.dropPrefix with
    ⟨prefixDomains, suffixSource, suffixTarget, hprefixLength,
      Hsource, htarget, Hsuffix⟩
  have hsuffixArity : n - i = (n - i - 1) + 1 := by omega
  rw [hsuffixArity] at Hsuffix
  cases Hsuffix with
  | @cons _ sourceDomain domainTarget sourceBody arity bodyTarget name bi
      Hdomain HdomainType Hbody =>
    exact ⟨prefixDomains, _, name, sourceDomain, sourceBody, bi,
      domainTarget, bodyTarget, hprefixLength, Hsource, rfl, htarget,
      Hdomain, HdomainType, Hbody⟩

/-- Select a binder when the complete abstract target telescope is already
known.  This identifies the selected target domain itself, rather than only
returning an existential domain from structural inversion. -/
theorem Expr.ForallTelescopeTypeTranslation.binderAt_target
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ source n target)
    (domains : List VExpr) (result : VExpr)
    (htarget : target = VExpr.wrapForalls domains result)
    (hlength : domains.length = n)
    (i : Nat) (hi : i < n) :
    ∃ suffixSource name sourceDomain sourceBody bi bodyTarget,
      Expr.ForallTelescope source i suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext (domains.take i) Δ)
        sourceDomain domains[i] ∧
      env.IsType Us.length
        (abstractForallContext (domains.take i) Δ).toCtx domains[i] ∧
      Expr.ForallTelescopeTypeTranslation env Us
        ((none, .vlam domains[i]) ::
          abstractForallContext (domains.take i) Δ)
        sourceBody (n - i - 1) bodyTarget := by
  rcases H.binderAt i hi with
    ⟨prefixDomains, suffixSource, name, sourceDomain, sourceBody, bi,
      domainTarget, bodyTarget, hprefixLength, Hsource, hsource,
      htarget', Hdomain, HdomainType, Hbody⟩
  have hidomains : i < domains.length := by omega
  have hsplit : domains = domains.take i ++ domains[i] ::
      domains.drop (i + 1) := by
    calc
      domains = domains.take (i + 1) ++ domains.drop (i + 1) :=
        (List.take_append_drop (i + 1) domains).symm
      _ = (domains.take i ++ [domains[i]]) ++ domains.drop (i + 1) := by
        rw [List.take_append_getElem hidomains]
      _ = domains.take i ++ domains[i] :: domains.drop (i + 1) := by
        simp
  have hprefix : prefixDomains = domains.take i := by
    apply VExpr.wrapForalls_prefix_domains_eq hprefixLength
      (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidomains)])
    calc
      VExpr.wrapForalls prefixDomains (.forallE domainTarget bodyTarget) =
          target := htarget'.symm
      _ = VExpr.wrapForalls domains result := htarget
      _ = VExpr.wrapForalls
          (domains.take i ++ domains[i] :: domains.drop (i + 1)) result := by
        rw [← hsplit]
  subst prefixDomains
  have hsuffix : .forallE domainTarget bodyTarget =
      VExpr.wrapForalls (domains[i] :: domains.drop (i + 1)) result := by
    apply VExpr.wrapForalls_left_cancel (domains.take i)
    calc
      VExpr.wrapForalls (domains.take i) (.forallE domainTarget bodyTarget) =
          target := htarget'.symm
      _ = VExpr.wrapForalls domains result := htarget
      _ = VExpr.wrapForalls
          (domains.take i ++ domains[i] :: domains.drop (i + 1)) result := by
        rw [← hsplit]
      _ = VExpr.wrapForalls (domains.take i)
          (VExpr.wrapForalls (domains[i] :: domains.drop (i + 1)) result) := by
        exact VExpr.wrapForalls_append _ _ _
  simp only [VExpr.wrapForalls] at hsuffix
  injection hsuffix with hdomainTarget _hbodyTarget
  subst domainTarget
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType, Hbody⟩

/-- Two translated forall telescopes have definitionally equal abstract
prefix contexts whenever their concrete binder domains agree pointwise.
The bodies and the remaining telescope arities may differ; dependency is
handled by extending the context conversion one translated binder at a
time. -/
theorem Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtx
    (Henv : env.WF)
    (H₁ : Expr.ForallTelescopeTypeTranslation env Us []
      source₁ arity₁ target₁)
    (H₂ : Expr.ForallTelescopeTypeTranslation env Us []
      source₂ arity₂ target₂)
    (domains₁ domains₂ : List VExpr) (result₁ result₂ : VExpr)
    (htarget₁ : target₁ = VExpr.wrapForalls domains₁ result₁)
    (htarget₂ : target₂ = VExpr.wrapForalls domains₂ result₂)
    (hlength₁ : domains₁.length = arity₁)
    (hlength₂ : domains₂.length = arity₂)
    (prefixLen : Nat) (hprefix₁ : prefixLen ≤ arity₁)
    (hprefix₂ : prefixLen ≤ arity₂)
    (Hdomains : ∀ i (_hiprefix : i < prefixLen)
      (_hi₁ : i < arity₁) (_hi₂ : i < arity₂)
      {domain₁ domain₂ : Expr},
      Expr.ForallBinderAt source₁ i domain₁ →
      Expr.ForallBinderAt source₂ i domain₂ →
      domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      (domains₁.take prefixLen).reverse
      (domains₂.take prefixLen).reverse := by
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have habstractToCtx : ∀ types : List VExpr,
      (abstractForallContext types []).toCtx = types.reverse := by
    intro types
    simp only [abstractForallContext, List.append_nil]
    exact htoCtx types.reverse
  induction prefixLen with
  | zero => exact .zero
  | succ prefixLen ih =>
    have hi₁ : prefixLen < arity₁ := by omega
    have hi₂ : prefixLen < arity₂ := by omega
    have hdom₁ : prefixLen < domains₁.length := by omega
    have hdom₂ : prefixLen < domains₂.length := by omega
    have Hprior := ih (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by omega) hi₁ hi₂ Hbinder₁ Hbinder₂)
    rcases H₁.binderAt_target domains₁ result₁ htarget₁ hlength₁
        prefixLen hi₁ with
      ⟨suffix₁, name₁, sourceDomain₁, sourceBody₁, bi₁, bodyTarget₁,
        Hsource₁, hsuffix₁, Hdomain₁, _HdomainType₁, _Hbody₁⟩
    rcases H₂.binderAt_target domains₂ result₂ htarget₂ hlength₂
        prefixLen hi₂ with
      ⟨suffix₂, name₂, sourceDomain₂, sourceBody₂, bi₂, bodyTarget₂,
        Hsource₂, hsuffix₂, Hdomain₂, _HdomainType₂, _Hbody₂⟩
    have hsourceDomain : sourceDomain₁ = sourceDomain₂ :=
      Hdomains prefixLen (Nat.lt_succ_self _) hi₁ hi₂
        (Hsource₁.binderAt hsuffix₁) (Hsource₂.binderAt hsuffix₂)
    rw [← hsourceDomain] at Hdomain₂
    have Hvlctx := abstractForallContext.isDefEq Hprior
    have HdomainU := Hdomain₁.uniq Henv Hvlctx Hdomain₂
    rcases _HdomainType₁ with ⟨level, HdomainType₁⟩
    have HdomainU' : env.IsDefEqU Us.length
        (domains₁.take prefixLen).reverse
        domains₁[prefixLen] domains₂[prefixLen] := by
      rw [habstractToCtx] at HdomainU
      exact HdomainU
    have HdomainType₁' : env.HasType Us.length
        (domains₁.take prefixLen).reverse domains₁[prefixLen]
        (.sort level) := by
      rw [habstractToCtx] at HdomainType₁
      exact HdomainType₁
    have Hdomain' := HdomainU'.of_l Henv Hprior.isType HdomainType₁'
    have Hnext : VEnv.IsDefEqCtx env Us.length []
        (domains₁[prefixLen] :: (domains₁.take prefixLen).reverse)
        (domains₂[prefixLen] :: (domains₂.take prefixLen).reverse) :=
      .succ Hprior Hdomain'
    have htake₁ : domains₁.take (prefixLen + 1) =
        domains₁.take prefixLen ++ [domains₁[prefixLen]] := by
      exact (List.take_append_getElem hdom₁).symm
    have htake₂ : domains₂.take (prefixLen + 1) =
        domains₂.take prefixLen ++ [domains₂[prefixLen]] := by
      exact (List.take_append_getElem hdom₂).symm
    rw [htake₁, htake₂]
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append] using Hnext

/-- Base-context form of `commonPrefixDefEqCtx`.  The two translations may
start over independently produced anonymous telescopes, provided those base
telescopes are already definitionally equal.  Each selected binder extends
that conversion, so dependency in all later domains is preserved. -/
theorem Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
    (Henv : env.WF)
    (Hbase : VEnv.IsDefEqCtx env Us.length []
      base₁.reverse base₂.reverse)
    (H₁ : Expr.ForallTelescopeTypeTranslation env Us
      (abstractForallContext base₁ []) source₁ arity₁ target₁)
    (H₂ : Expr.ForallTelescopeTypeTranslation env Us
      (abstractForallContext base₂ []) source₂ arity₂ target₂)
    (domains₁ domains₂ : List VExpr) (result₁ result₂ : VExpr)
    (htarget₁ : target₁ = VExpr.wrapForalls domains₁ result₁)
    (htarget₂ : target₂ = VExpr.wrapForalls domains₂ result₂)
    (hlength₁ : domains₁.length = arity₁)
    (hlength₂ : domains₂.length = arity₂)
    (prefixLen : Nat) (hprefix₁ : prefixLen ≤ arity₁)
    (hprefix₂ : prefixLen ≤ arity₂)
    (Hdomains : ∀ i (_hiprefix : i < prefixLen)
      (_hi₁ : i < arity₁) (_hi₂ : i < arity₂)
      {domain₁ domain₂ : Expr},
      Expr.ForallBinderAt source₁ i domain₁ →
      Expr.ForallBinderAt source₂ i domain₂ →
      domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      ((domains₁.take prefixLen).reverse ++ base₁.reverse)
      ((domains₂.take prefixLen).reverse ++ base₂.reverse) := by
  have habstractToCtx : ∀ (base types : List VExpr),
      (abstractForallContext types
        (abstractForallContext base [])).toCtx =
        types.reverse ++ base.reverse := by
    intro base types
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  induction prefixLen with
  | zero => simpa using Hbase
  | succ prefixLen ih =>
    have hi₁ : prefixLen < arity₁ := by omega
    have hi₂ : prefixLen < arity₂ := by omega
    have hdom₁ : prefixLen < domains₁.length := by omega
    have hdom₂ : prefixLen < domains₂.length := by omega
    have Hprior := ih (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by omega) hi₁ hi₂ Hbinder₁ Hbinder₂)
    rcases H₁.binderAt_target domains₁ result₁ htarget₁ hlength₁
        prefixLen hi₁ with
      ⟨suffix₁, name₁, sourceDomain₁, sourceBody₁, bi₁, bodyTarget₁,
        Hsource₁, hsuffix₁, Hdomain₁, HdomainType₁, _Hbody₁⟩
    rcases H₂.binderAt_target domains₂ result₂ htarget₂ hlength₂
        prefixLen hi₂ with
      ⟨suffix₂, name₂, sourceDomain₂, sourceBody₂, bi₂, bodyTarget₂,
        Hsource₂, hsuffix₂, Hdomain₂, _HdomainType₂, _Hbody₂⟩
    have hsourceDomain : sourceDomain₁ = sourceDomain₂ :=
      Hdomains prefixLen (Nat.lt_succ_self _) hi₁ hi₂
        (Hsource₁.binderAt hsuffix₁) (Hsource₂.binderAt hsuffix₂)
    rw [← hsourceDomain] at Hdomain₂
    have Hvlctx : VLCtx.IsDefEq env Us.length
        (abstractForallContext (domains₁.take prefixLen)
          (abstractForallContext base₁ []))
        (abstractForallContext (domains₂.take prefixLen)
          (abstractForallContext base₂ [])) := by
      have Hanonymous := abstractForallContext.isDefEq
        (left := base₁ ++ domains₁.take prefixLen)
        (right := base₂ ++ domains₂.take prefixLen) (by
          simpa [List.reverse_append, List.append_assoc] using Hprior)
      simpa [abstractForallContext, List.reverse_append,
        List.map_append, List.append_assoc] using Hanonymous
    have HdomainU := Hdomain₁.uniq Henv Hvlctx Hdomain₂
    rcases HdomainType₁ with ⟨level, HdomainType₁⟩
    have HdomainU' : env.IsDefEqU Us.length
        ((domains₁.take prefixLen).reverse ++ base₁.reverse)
        domains₁[prefixLen] domains₂[prefixLen] := by
      rw [habstractToCtx] at HdomainU
      exact HdomainU
    have HdomainType₁' : env.HasType Us.length
        ((domains₁.take prefixLen).reverse ++ base₁.reverse)
        domains₁[prefixLen] (.sort level) := by
      rw [habstractToCtx] at HdomainType₁
      exact HdomainType₁
    have Hdomain' := HdomainU'.of_l Henv Hprior.isType HdomainType₁'
    have Hnext : VEnv.IsDefEqCtx env Us.length []
        (domains₁[prefixLen] ::
          (domains₁.take prefixLen).reverse ++ base₁.reverse)
        (domains₂[prefixLen] ::
          (domains₂.take prefixLen).reverse ++ base₂.reverse) :=
      .succ Hprior Hdomain'
    have htake₁ : domains₁.take (prefixLen + 1) =
        domains₁.take prefixLen ++ [domains₁[prefixLen]] := by
      exact (List.take_append_getElem hdom₁).symm
    have htake₂ : domains₂.take (prefixLen + 1) =
        domains₂.take prefixLen ++ [domains₂[prefixLen]] := by
      exact (List.take_append_getElem hdom₂).symm
    rw [htake₁, htake₂]
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc] using Hnext

/-- A translated telescope that is a type has a binder-by-binder translation. -/
theorem Expr.ForallTelescopeTypeTranslation.ofTrExprS
    (Htel : Expr.ForallTelescope e n residual)
    (Htr : TrExprS env Us Δ e e')
    (Htype : env.IsType Us.length Δ.toCtx e') :
    Expr.ForallTelescopeTypeTranslation env Us Δ e n e' := by
  induction Htel generalizing Δ e' with
  | nil => exact .nil Htr Htype
  | cons Htail ih =>
    cases Htr with
    | forallE HdomType HbodyType Hdom Hbody =>
      exact .cons Hdom HdomType (ih Hbody HbodyType)


theorem List.exists_append_five_of_length_eq
    (xs : List α) (a b c d e : Nat)
    (h : xs.length = a + b + c + d + e) :
    ∃ as bs cs ds es,
      xs = as ++ bs ++ cs ++ ds ++ es ∧
      as.length = a ∧ bs.length = b ∧ cs.length = c ∧
      ds.length = d ∧ es.length = e := by
  let as := xs.take a
  let restA := xs.drop a
  let bs := restA.take b
  let restB := restA.drop b
  let cs := restB.take c
  let restC := restB.drop c
  let ds := restC.take d
  let es := restC.drop d
  refine ⟨as, bs, cs, ds, es, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [as, bs, cs, ds, es, restA, restB, restC]
    symm
    simp only [List.append_assoc]
    rw [List.take_append_drop d, List.take_append_drop c,
      List.take_append_drop b, List.take_append_drop a]
  all_goals (simp [as, bs, cs, ds, es, restA, restB, restC, h]; omega)

private theorem vlamPrefix_find_bvar
    (pref : List VExpr) (Δ : VLCtx) (i : Nat) (hi : i < pref.length) :
    ∃ type, VLCtx.find? ((pref.map fun type =>
      ((none, VLocalDecl.vlam type) :
        Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ)
      (Sum.inl i) = some (VExpr.bvar i, type) := by
  induction pref generalizing i with
  | nil => simp at hi
  | cons type pref ih =>
    cases i with
    | zero =>
      refine ⟨type.lift, ?_⟩
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
    | succ i =>
      have hi' : i < pref.length := by simpa using hi
      rcases ih i hi' with ⟨found, hfind⟩
      refine ⟨found.lift, ?_⟩
      simp only [List.map_cons, List.cons_append, VLCtx.find?, VLCtx.next]
      rw [hfind]
      simp [VLocalDecl.depth, VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm]

theorem abstractForallContext.find?_bvar
    (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    ∃ type, VLCtx.find? (abstractForallContext domains Δ) (.inl i) =
      some (.bvar i, type) := by
  apply vlamPrefix_find_bvar domains.reverse Δ i
  simpa using hi

/-- Every in-range source de Bruijn variable translates to the identically
numbered abstract variable in an anonymous forall context. -/
theorem TrExprS.bvar_of_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    TrExprS env Us (abstractForallContext domains Δ)
      (.bvar i) (.bvar i) := by
  rcases abstractForallContext.find?_bvar domains Δ i hi with
    ⟨type, hfind⟩
  exact .bvar hfind

/-- The bvar spine of length `n` translates pointwise in any abstract forall context with
at least `n` domains. -/
theorem TrExprS.bvarSpine_of_abstractForallContext
    (domains : List VExpr) (Δ : VLCtx) (n : Nat)
    (hn : n ≤ domains.length) :
    List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
      (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i))
      (List.ofFn fun i : Fin n => VExpr.bvar (n - 1 - i)) := by
  apply List.forall₂_of_getElem (by simp)
  intro i hsource htarget
  have hi : i < n := by simpa using hsource
  simp only [List.getElem_ofFn]
  apply TrExprS.bvar_of_abstractForallContext
  omega

theorem TrExprS.bvar_eq_of_abstractForallContext
    (H : TrExprS env Us (abstractForallContext domains Δ) (.bvar i) out)
    (hi : i < domains.length) : out = .bvar i := by
  cases H with
  | bvar hfind =>
    rcases abstractForallContext.find?_bvar domains Δ i hi with
      ⟨type, hcanonical⟩
    rw [hcanonical] at hfind
    exact (congrArg Prod.fst (Option.some.inj hfind)).symm

theorem TrExprS.foldl_bvars_eq
    (domains : List VExpr) (Δ : VLCtx)
    (args : List Nat) (hargs : ∀ i ∈ args, i < domains.length)
    (base : Expr) (vbase : VExpr)
    (hbase : ∀ out, TrExprS env Us (abstractForallContext domains Δ)
      base out → out = vbase)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (args.foldl (fun fn i => .app fn (.bvar i)) base) out) :
    out = args.foldl (fun fn i => .app fn (.bvar i)) vbase := by
  induction args generalizing base vbase with
  | nil => exact hbase out H
  | cons i args ih =>
    apply ih (fun j hj => hargs j (by simp [hj]))
      (.app base (.bvar i)) (.app vbase (.bvar i))
    · intro result Hresult
      cases Hresult with
      | app _ _ hfn harg =>
        rw [hbase _ hfn,
          TrExprS.bvar_eq_of_abstractForallContext harg
            (hargs i (by simp))]
    · exact H


/-- Reuse the checked domain translations of a forall telescope to
translate a lambda telescope with the same literal source binder prefix.
Only the lambda residual is supplied independently. -/
theorem Expr.SameForallLambdaPrefix.translateLambda
    (Hsame : Expr.SameForallLambdaPrefix n forallSource lambdaSource)
    (HforallTelescope : Expr.ForallTelescope
      forallSource n forallResidual)
    (HlambdaTelescope : Expr.LambdaTelescope
      lambdaSource n lambdaResidual)
    (hdomains : domains.length = n)
    (Hforall : TrExprS env Us Delta forallSource
      (VExpr.wrapForalls domains forallTarget))
    (HlambdaResidual : TrExprS env Us
      (abstractForallContext domains Delta) lambdaResidual lambdaTarget) :
    TrExprS env Us Delta lambdaSource
      (VExpr.wrapLams domains lambdaTarget) := by
  induction Hsame generalizing domains Delta forallResidual lambdaResidual
      forallTarget lambdaTarget with
  | nil =>
    cases HforallTelescope
    cases HlambdaTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using HlambdaResidual
  | @cons n forallBody lambdaBody name dom bi Hsame ih =>
    cases HforallTelescope with
    | cons HforallTail =>
      cases HlambdaTelescope with
      | cons HlambdaTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Hforall with
          | forallE HdomainType _ HdomainTr HforallBody =>
            apply TrExprS.lam HdomainType HdomainTr
            have htail : domains.length = n := by simpa using hdomains
            simpa [VExpr.wrapLams, abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HforallTail HlambdaTail htail HforallBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HlambdaResidual)

/-- Reuse the binder-domain part of one lambda translation with a different
residual body.  The two source telescopes share their concrete prefix, so the
template derivation supplies the exact translated domains and their type
proofs; only the independently translated residual is replaced. -/
theorem Expr.SameLambdaPrefix.replaceTranslatedResidual
    (Hsame : Expr.SameLambdaPrefix n template replacement)
    (HtemplateTelescope : Expr.LambdaTelescope template n templateResidual)
    (HreplacementTelescope :
      Expr.LambdaTelescope replacement n replacementResidual)
    (hdomains : domains.length = n)
    (Htemplate :
      TrExprS env Us Delta template (VExpr.wrapLams domains templateTarget))
    (HreplacementResidual :
      TrExprS env Us (abstractForallContext domains Delta)
        replacementResidual replacementTarget) :
    TrExprS env Us Delta replacement
      (VExpr.wrapLams domains replacementTarget) := by
  induction Hsame generalizing domains Delta templateResidual
      replacementResidual templateTarget replacementTarget with
  | nil =>
    cases HtemplateTelescope
    cases HreplacementTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using HreplacementResidual
  | @cons n left right name dom bi Hsame ih =>
    cases HtemplateTelescope with
    | cons HtemplateTail =>
      cases HreplacementTelescope with
      | cons HreplacementTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Htemplate with
          | lam HdomainType HdomainTr HtemplateBody =>
            have htail : domains.length = n := by simpa using hdomains
            apply TrExprS.lam HdomainType HdomainTr
            change TrExprS env Us ((none, .vlam domain) :: Delta) right
              (VExpr.wrapLams domains replacementTarget)
            simpa [abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HtemplateTail HreplacementTail htail HtemplateBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidual)


/-- Translation of a lambda telescope retains its arity and exposes the
residual translation beneath precisely the corresponding abstract binders. -/
theorem TrExprS.lambdaTelescope_shape_with_context
    (Htel : Expr.LambdaTelescope e arity residual)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Δ)
        residual residual' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr⟩
  | @cons body arity residual name dom bi Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with
        ⟨domains, residual', hlength, heq, hresidual⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual

/-- Exact-target telescope inversion.  When the translated target is already
presented with the right number of lambdas, syntax-directedness exposes the
residual under precisely those domains, without introducing existentially
chosen replacements. -/
theorem TrExprS.lambdaTelescope_exact_residual
    (Htel : Expr.LambdaTelescope e arity residual)
    (hdomains : domains.length = arity)
    (Htr : TrExprS env Us Δ e (VExpr.wrapLams domains target)) :
    TrExprS env Us (abstractForallContext domains Δ) residual target := by
  induction Htel generalizing domains Δ with
  | nil =>
    have : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapLams] using Htr
  | @cons body arity residual name dom bi Htel ih =>
    cases domains with
    | nil => simp at hdomains
    | cons domain domains =>
      cases Htr with
      | @lam domain' body' =>
        rename_i _ _ _ hbody
        have htail : domains.length = arity := by simpa using hdomains
        simpa [abstractForallContext, List.map_append, List.append_assoc]
          using ih htail hbody

/-- The target domains exposed by a translated lambda telescope form a
well-formed extension of the starting verification context. -/
theorem TrExprS.lambdaTelescope_contextWF
    (Htel : Expr.LambdaTelescope e arity residual)
    (hdomains : domains.length = arity)
    (Htr : TrExprS env Us Δ e (VExpr.wrapLams domains target))
    (hDelta : Δ.WF env Us.length) :
    (abstractForallContext domains Δ).WF env Us.length := by
  induction Htel generalizing domains Δ with
  | nil =>
      have : domains = [] := List.eq_nil_of_length_eq_zero hdomains
      subst domains
      simpa [abstractForallContext] using hDelta
  | @cons body arity residual name dom bi Htel ih =>
      cases domains with
      | nil => simp at hdomains
      | cons domain domains =>
        cases Htr with
        | lam HdomainType _ HbodyTr =>
          have htail : domains.length = arity := by simpa using hdomains
          have hnext : VLCtx.WF env Us.length
              ((none, VLocalDecl.vlam domain) :: Δ) :=
            ⟨hDelta, by simp, HdomainType⟩
          simpa [abstractForallContext, List.reverse_cons,
            List.map_append, List.append_assoc] using
              ih htail HbodyTr hnext


end VerifyInductive
end Lean4Lean
