import Lean4Lean.Verify.Inductive.Nested.Lowering.Basic

/-! An exact, cache-independent specification of `Expr.replace` (`ExprReplacement`), the
telescope accepted by nested restoration (`RestoreTelescope`), and the binder-by-binder
decomposition of a generated recursor type (`RecursorTypeTelescope`) used to transport
restored recursor types (section 3.3 of the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact, cache-independent specification of `Expr.replace`. A successful
node callback stops traversal at that node; otherwise the relation records
the recursively restored children and the same update combinators used by
Lean's implementation. -/
inductive ExprReplacement (replaceNode : Expr → Option Expr) : Expr → Expr → Prop
  | occurrence (h : replaceNode input = some output) :
      ExprReplacement replaceNode input output
  | bvar (h : replaceNode (.bvar i) = none) :
      ExprReplacement replaceNode (.bvar i) (.bvar i)
  | fvar {fvarId : FVarId} (h : replaceNode (.fvar fvarId) = none) :
      ExprReplacement replaceNode (.fvar fvarId) (.fvar fvarId)
  | mvar {mvarId : MVarId} (h : replaceNode (.mvar mvarId) = none) :
      ExprReplacement replaceNode (.mvar mvarId) (.mvar mvarId)
  | sort (h : replaceNode (.sort level) = none) :
      ExprReplacement replaceNode (.sort level) (.sort level)
  | const (h : replaceNode (.const name levels) = none) :
      ExprReplacement replaceNode (.const name levels) (.const name levels)
  | lit (h : replaceNode (.lit literal) = none) :
      ExprReplacement replaceNode (.lit literal) (.lit literal)
  | app (h : replaceNode (.app fn arg) = none)
      (hfn : ExprReplacement replaceNode fn fn')
      (harg : ExprReplacement replaceNode arg arg') :
      ExprReplacement replaceNode (.app fn arg)
        (Expr.updateApp! (.app fn arg) fn' arg')
  | lam (h : replaceNode (.lam name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.lam name dom body bi)
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body')
  | forallE (h : replaceNode (.forallE name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.forallE name dom body bi)
        (Expr.updateForallE! (.forallE name dom body bi) dom' body')
  | letE (h : replaceNode (.letE name type value body nondep) = none)
      (htype : ExprReplacement replaceNode type type')
      (hvalue : ExprReplacement replaceNode value value')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.letE name type value body nondep)
        (Expr.updateLetE! (.letE name type value body nondep)
          type' value' body')
  | mdata (h : replaceNode (.mdata data body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.mdata data body)
        (Expr.updateMData! (.mdata data body) body')
  | proj (h : replaceNode (.proj typeName index body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.proj typeName index body)
        (Expr.updateProj! (.proj typeName index body) body')

/-- Residual-sensitive form of `forallTelescope`: replacement below the
leading binders is retained as an explicit relation between the old and new
residual expressions. -/
theorem ExprReplacement.forallTelescope_residual
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      Expr.ForallTelescope output arity restoredResidual ∧
      ExprReplacement replaceNode residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil output, Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | occurrence h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored, Hresidual⟩
      refine ⟨restoredResidual, ?_, Hresidual⟩
      simpa [Expr.updateForallE!] using
        (Expr.ForallTelescope.cons (name := name) (dom := _)
          (bi := bi) Hrestored)

/-- Binder-aligned form of expression replacement.  Unlike the existential
`forallTelescope_residual` theorem, this relation retains the replacement
proof for every old/restored domain and for the final residual. -/
inductive ExprReplacement.ForallTelescopeReplacement
    (replaceNode : Expr → Option Expr) :
    Expr → Expr → Nat → Expr → Expr → Prop
  | nil (Hbody : ExprReplacement replaceNode oldBody newBody) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody 0 oldBody newBody
  | cons
      (Hnone : replaceNode (.forallE name oldDom oldBody bi) = none)
      (Hdom : ExprReplacement replaceNode oldDom newDom)
      (Hbody : ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody arity oldResidual newResidual) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        (.forallE name oldDom oldBody bi)
        (Expr.updateForallE! (.forallE name oldDom oldBody bi)
          newDom newBody)
        (arity + 1) oldResidual newResidual

/-- Decompose a replacement of a known forall telescope into the
binder-aligned `ForallTelescopeReplacement`. -/
theorem ExprReplacement.forallTelescopeReplacement
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      ExprReplacement.ForallTelescopeReplacement replaceNode input output
        arity residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | occurrence h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored⟩
      exact ⟨restoredResidual, .cons h hdom Hrestored⟩

theorem ExprReplacement.ForallTelescopeReplacement.newTelescope
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    Expr.ForallTelescope output arity newResidual := by
  induction H with
  | nil => exact .nil _
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    simpa [Expr.updateForallE!] using
      (Expr.ForallTelescope.cons (name := name) (dom := newDom)
        (bi := bi) ih)

theorem ExprReplacement.ForallTelescopeReplacement.residualReplacement
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    ExprReplacement replaceNode oldResidual newResidual := by
  induction H with
  | nil Hbody => exact Hbody
  | cons _ _ _ ih => exact ih

theorem ExprReplacement.ofReplace
    (replaceNode : Expr → Option Expr) :
    ∀ input, ExprReplacement replaceNode input (input.replace replaceNode) := by
  intro input
  induction input with
  | bvar i =>
    cases h : replaceNode (.bvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.bvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | fvar i =>
    cases h : replaceNode (.fvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.fvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | mvar i =>
    cases h : replaceNode (.mvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.mvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | sort level =>
    cases h : replaceNode (.sort level) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.sort h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | const name levels =>
    cases h : replaceNode (.const name levels) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.const h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | lit literal =>
    cases h : replaceNode (.lit literal) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.lit h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | app fn arg hfn harg =>
    cases h : replaceNode (.app fn arg) with
    | none =>
      rw [Expr.replace_eq] at hfn harg
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .app h hfn harg
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)

  | lam name dom body bi hdom hbody =>
    cases h : replaceNode (.lam name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .lam h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | forallE name dom body bi hdom hbody =>
    cases h : replaceNode (.forallE name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .forallE h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | letE name type value body nondep htype hvalue hbody =>
    cases h : replaceNode (.letE name type value body nondep) with
    | none =>
      rw [Expr.replace_eq] at htype hvalue hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .letE h htype hvalue hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | mdata data body hbody =>
    cases h : replaceNode (.mdata data body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .mdata h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | proj typeName index body hbody =>
    cases h : replaceNode (.proj typeName index body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .proj h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)

/-- The relational restoration traversal is functional and computes exactly
`Expr.replace`. This lets the inverse theorems for restoration use the
`ExprReplacement` derivation recorded by `NestedRestoration`. -/
theorem ExprReplacement.eq_replace
    (H : ExprReplacement replaceNode input output) :
    output = input.replace replaceNode := by
  induction H with
  | occurrence h => simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | bvar h | fvar h | mvar h | sort h | const h | lit h =>
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | app h hfn harg ihFn ihArg =>
    rw [Expr.replace_eq] at ihFn ihArg
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihFn, ← ihArg]
  | lam h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | forallE h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | letE h htype hvalue hbody ihType ihValue ihBody =>
    rw [Expr.replace_eq] at ihType ihValue ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihType, ← ihValue, ← ihBody]
  | mdata h hbody ihBody | proj h hbody ihBody =>
    rw [Expr.replace_eq] at ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihBody]

/-- The body traversal used by `restoreNested` is related exactly to its
three separately specified node-restoration cases. -/
theorem restoreNested_body
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (body : Expr) :
    ExprReplacement (result.restoreNestedNode env As auxRec) body
      (body.replace (result.restoreNestedNode env As auxRec)) :=
  ExprReplacement.ofReplace _ body

/-- Mixed forall/lambda telescope accepted by nested restoration. The
executable preserves the outer binder kind of the input root, while both
binder forms are accepted during opening. -/
inductive RestoreTelescope : Expr → Nat → Prop
  | done : RestoreTelescope e 0
  | forallE : RestoreTelescope body n →
      RestoreTelescope (.forallE name dom body bi) (n + 1)
  | lam : RestoreTelescope body n →
      RestoreTelescope (.lam name dom body bi) (n + 1)

theorem Expr.ForallTelescope.inferImplicit
    (H : Expr.ForallTelescope e arity residual)
    (max : Nat) (inferBinderTypes : Bool) :
    ∃ residual',
      Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
        residual' := by
  induction max generalizing e arity residual with
  | zero => exact ⟨residual, by simpa [Expr.inferImplicit] using H⟩
  | succ max ih =>
    cases H with
    | nil => exact ⟨_, .nil _⟩
    | cons Htail =>
      rcases ih Htail with ⟨residual', Htail'⟩
      exact ⟨residual', by
        simp only [Expr.inferImplicit]
        exact Expr.ForallTelescope.cons Htail'⟩

/-- `inferImplicit` changes binder annotations only, so the terminal
expression of a forall telescope is preserved literally. -/
theorem Expr.ForallTelescope.inferImplicit_sameResidual
    (H : Expr.ForallTelescope e arity residual)
    (Hresidual : residual.isForall = false)
    (max : Nat) (inferBinderTypes : Bool) :
    Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
      residual := by
  induction max generalizing e arity residual with
  | zero => simpa [Expr.inferImplicit] using H
  | succ max ih =>
    cases H with
    | nil =>
      have heq : e.inferImplicit (max + 1) inferBinderTypes = e := by
        cases e <;> simp_all [Expr.inferImplicit, Expr.isForall]
      rw [heq]
      exact .nil _
    | cons Htail =>
      simp only [Expr.inferImplicit]
      exact Expr.ForallTelescope.cons (ih Htail Hresidual)

/-- Any prefix of a generated forall telescope is accepted by nested
restoration. -/
theorem Expr.ForallTelescope.restorePrefix
    (H : Expr.ForallTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | cons Hbody =>
      apply RestoreTelescope.forallE
      exact ih Hbody (by omega)

/-- Any prefix of a generated lambda telescope is accepted by nested
restoration. -/
theorem Expr.LambdaTelescope.restorePrefix
    (H : Expr.LambdaTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | @cons body arity residual name dom bi Hbody =>
      apply RestoreTelescope.lam
      exact ih Hbody (by omega)

/-- Executable iota right-hand sides always expose at least the common-parameter
lambda prefix opened by `restoreNested`. -/
theorem RecursorRuleSyntax.rhsRestoreTelescope
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope rule.rhs nparams := by
  apply H.rhsLambdaTelescope.restorePrefix
  rw [hparams]
  have hp : stats.params.size = H.params_bound.fvars.length := by
    simpa using congrArg Array.size H.params_bound.expressions
  unfold RecursorRuleSyntax.binders
  simp only [List.length_append]
  omega

/-- The executable recursor type exposes the same parameter prefix that was
bound while generating its telescope. -/
theorem GeneratedRecursorEntry.typeRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hparams : CDeclArray c.lctx stats.params)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope H.info.type nparams := by
  rw [H.type, hparams]
  rcases (Hparams.forallTelescope _).inferImplicit 1000 false with
    ⟨residual, Htelescope⟩
  exact Htelescope.restorePrefix (Nat.le_refl _)

/-- Binder-by-binder translation of a generated recursor type.
The five lists are the abstract domains corresponding respectively to the
executable parameter, motive, minor, index, and major binder groups. Keeping
the translated residual in their abstract context makes explicit the pieces
that are transported across nested restoration. -/
structure RecursorTypeTelescope
    (env : VEnv) (Us : List Name) (source : Expr) (target : VExpr)
    (numParams numMotives numMinors numIndices ownerIdx : Nat) where
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  result : VExpr
  target_eq : target = VExpr.wrapForalls
    (params ++ motives ++ minors ++ indices ++ major) result
  params_length : params.length = numParams
  motives_length : motives.length = numMotives
  minors_length : minors.length = numMinors
  indices_length : indices.length = numIndices
  major_length : major.length = 1
  typed : Expr.ForallTelescopeTypeTranslation env Us [] source
    (numParams + numMotives + numMinors + numIndices + 1) target
  residual : TrExprS env Us
    (abstractForallContext
      (params ++ motives ++ minors ++ indices ++ major) [])
    (concreteRecursorResult numMotives numMinors numIndices ownerIdx) result

/-- Any two decompositions of the same translated recursor type have the same
complete domain list and residual, so facts proved for one decomposition apply
to any other. -/
theorem RecursorTypeTelescope.domainsResult_eq
    (T₁ T₂ : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁.params ++ T₁.motives ++ T₁.minors ++ T₁.indices ++ T₁.major =
        T₂.params ++ T₂.motives ++ T₂.minors ++ T₂.indices ++ T₂.major ∧
      T₁.result = T₂.result := by
  let domains₁ :=
    T₁.params ++ T₁.motives ++ T₁.minors ++ T₁.indices ++ T₁.major
  let domains₂ :=
    T₂.params ++ T₂.motives ++ T₂.minors ++ T₂.indices ++ T₂.major
  have hlength₁ : domains₁.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₁, List.length_append, T₁.params_length,
      T₁.motives_length, T₁.minors_length, T₁.indices_length,
      T₁.major_length]
  have hlength₂ : domains₂.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₂, List.length_append, T₂.params_length,
      T₂.motives_length, T₂.minors_length, T₂.indices_length,
      T₂.major_length]
  have hwrapped : VExpr.wrapForalls domains₁ T₁.result =
      VExpr.wrapForalls domains₂ T₂.result := by
    rw [← T₁.target_eq, ← T₂.target_eq]
  have hdomains : domains₁ = domains₂ := by
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hlength₁ hlength₂ (by simpa using hwrapped)
  refine ⟨by simpa [domains₁, domains₂] using hdomains, ?_⟩
  apply VExpr.wrapForalls_left_cancel domains₂
  rw [hdomains] at hwrapped
  exact hwrapped

/-- Groupwise form of `domainsResult_eq`, using the five fixed executable
arities to recover each telescope component. -/
theorem RecursorTypeTelescope.groupsResult_eq
    (T₁ T₂ : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁.params = T₂.params ∧ T₁.motives = T₂.motives ∧
      T₁.minors = T₂.minors ∧ T₁.indices = T₂.indices ∧
      T₁.major = T₂.major ∧ T₁.result = T₂.result := by
  have H := T₁.domainsResult_eq T₂
  have H₀ : T₁.params ++
        (T₁.motives ++ (T₁.minors ++ (T₁.indices ++ T₁.major))) =
      T₂.params ++
        (T₂.motives ++ (T₂.minors ++ (T₂.indices ++ T₂.major))) := by
    simpa [List.append_assoc] using H.1
  have hparamsLength : T₁.params.length = T₂.params.length := by
    rw [T₁.params_length, T₂.params_length]
  have hparams := List.append_inj_left H₀ hparamsLength
  have H₁ := List.append_inj_right H₀ hparamsLength
  have hmotivesLength : T₁.motives.length = T₂.motives.length := by
    rw [T₁.motives_length, T₂.motives_length]
  have hmotives := List.append_inj_left H₁ hmotivesLength
  have H₂ := List.append_inj_right H₁ hmotivesLength
  have hminorsLength : T₁.minors.length = T₂.minors.length := by
    rw [T₁.minors_length, T₂.minors_length]
  have hminors := List.append_inj_left H₂ hminorsLength
  have H₃ := List.append_inj_right H₂ hminorsLength
  have hindicesLength : T₁.indices.length = T₂.indices.length := by
    rw [T₁.indices_length, T₂.indices_length]
  have hindices := List.append_inj_left H₃ hindicesLength
  have hmajor := List.append_inj_right H₃ hindicesLength
  exact ⟨hparams, hmotives, hminors, hindices, hmajor, H.2⟩

/-- Recursor-telescope translations are equal once their six computational
components are fixed. This strengthens `groupsResult_eq` from a rewriting
interface to equality of the structures, which is needed when later facts are
dependently indexed by the chosen telescope value. -/
theorem RecursorTypeTelescope.eq
    (T₁ T₂ : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁ = T₂ := by
  rcases T₁.groupsResult_eq T₂ with
    ⟨hparams, hmotives, hminors, hindices, hmajor, hresult⟩
  cases T₁
  cases T₂
  simp only at hparams hmotives hminors hindices hmajor hresult
  subst hparams
  subst hmotives
  subst hminors
  subst hindices
  subst hmajor
  subst hresult
  rfl

/-- The common parameter/motive/minor portions of two possibly different
mutual recursors are definitionally equal once their concrete source binder
domains are known to agree at those positions.  Owner-specific index/major
arities and residuals are deliberately allowed to differ. -/
theorem RecursorTypeTelescope.commonPrefixDefEqCtx
    (Henv : env.WF)
    (T₁ : RecursorTypeTelescope env Us source₁ target₁
      numParams numMotives numMinors numIndices₁ owner₁)
    (T₂ : RecursorTypeTelescope env Us source₂ target₂
      numParams numMotives numMinors numIndices₂ owner₂)
    (Hdomains : ∀ i,
      i < numParams + numMotives + numMinors →
      (hi₁ : i < numParams + numMotives + numMinors + numIndices₁ + 1) →
      (hi₂ : i < numParams + numMotives + numMinors + numIndices₂ + 1) →
      ∀ {domain₁ domain₂ : Expr},
        Expr.ForallBinderAt source₁ i domain₁ →
        Expr.ForallBinderAt source₂ i domain₂ →
        domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      (T₁.params ++ T₁.motives ++ T₁.minors).reverse
      (T₂.params ++ T₂.motives ++ T₂.minors).reverse := by
  let common := numParams + numMotives + numMinors
  let outer₁ := T₁.params ++ T₁.motives ++ T₁.minors
  let outer₂ := T₂.params ++ T₂.motives ++ T₂.minors
  let full₁ := outer₁ ++ T₁.indices ++ T₁.major
  let full₂ := outer₂ ++ T₂.indices ++ T₂.major
  have houter₁ : outer₁.length = common := by
    simp [outer₁, common, T₁.params_length, T₁.motives_length,
      T₁.minors_length] ; omega
  have houter₂ : outer₂.length = common := by
    simp [outer₂, common, T₂.params_length, T₂.motives_length,
      T₂.minors_length] ; omega
  have hfull₁ : full₁.length =
      numParams + numMotives + numMinors + numIndices₁ + 1 := by
    simp [full₁, outer₁, T₁.params_length, T₁.motives_length,
      T₁.minors_length, T₁.indices_length, T₁.major_length] ; omega
  have hfull₂ : full₂.length =
      numParams + numMotives + numMinors + numIndices₂ + 1 := by
    simp [full₂, outer₂, T₂.params_length, T₂.motives_length,
      T₂.minors_length, T₂.indices_length, T₂.major_length] ; omega
  have Hprefix := T₁.typed.commonPrefixDefEqCtx Henv T₂.typed
    full₁ full₂ T₁.result T₂.result
    (by simpa [full₁, outer₁, List.append_assoc] using T₁.target_eq)
    (by simpa [full₂, outer₂, List.append_assoc] using T₂.target_eq)
    hfull₁ hfull₂ common (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by simpa [common] using hiprefix)
        hi₁ hi₂ Hbinder₁ Hbinder₂)
  have htake₁ : full₁.take common = outer₁ := by
    rw [← houter₁]
    simp [full₁]
  have htake₂ : full₂.take common = outer₂ := by
    rw [← houter₂]
    simp [full₂]
  rw [htake₁, htake₂] at Hprefix
  simpa [outer₁, outer₂] using Hprefix

/-- Expose the source and abstract domains of the motive binder selected by
the recursor owner.  In particular, the domain is checked before later
motives, all minors, and the recursor's own index/major suffix have entered
the context. This is the structural half of the link to the motive telescope
of the recursor construction. -/
theorem RecursorTypeTelescope.ownerMotiveBinder
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < T.motives.length) :
    ∃ (suffixSource : Expr) (name : Name)
      (sourceDomain sourceBody : Expr) (bi : BinderInfo)
      (_bodyTarget : VExpr),
      Expr.ForallTelescope source (T.params.length + ownerIdx) suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext
          (T.params ++ T.motives.take ownerIdx) [])
        sourceDomain (T.motives[ownerIdx]'howner) ∧
      env.IsType Us.length
        (abstractForallContext
          (T.params ++ T.motives.take ownerIdx) []).toCtx
        (T.motives[ownerIdx]'howner) := by
  let domains := T.params ++
    (T.motives ++ (T.minors ++ (T.indices ++ T.major)))
  have hlength : domains.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length,
      T.major_length]
    omega
  have hposition : T.params.length + ownerIdx <
      numParams + numMotives + numMinors + numIndices + 1 := by
    rw [T.params_length, ← T.motives_length] at *
    omega
  have htarget : target = VExpr.wrapForalls domains T.result := by
    simpa only [domains, List.append_assoc] using T.target_eq
  rcases T.typed.binderAt_target domains T.result htarget hlength
      (T.params.length + ownerIdx) hposition with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType, _Hbody⟩
  have htake : domains.take (T.params.length + ownerIdx) =
      T.params ++ T.motives.take ownerIdx := by
    change (T.params ++
      (T.motives ++ (T.minors ++ (T.indices ++ T.major)))).take
        (T.params.length + ownerIdx) = _
    rw [List.take_length_add_append]
    rw [List.take_append_of_le_length (Nat.le_of_lt howner)]
  have hselected : domains[T.params.length + ownerIdx] =
      (T.motives[ownerIdx]'howner) := by
    simp only [domains]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left howner]
  rw [htake, hselected] at Hdomain HdomainType
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType⟩

/-- Expose the source and abstract domains of one flattened minor binder.
The domain is checked after all parameters and motives and the strictly
earlier minors, but before later minors and the owner-specific suffix. -/
theorem RecursorTypeTelescope.minorBinder
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (hminor : minorIdx < T.minors.length) :
    ∃ (suffixSource : Expr) (name : Name)
      (sourceDomain sourceBody : Expr) (bi : BinderInfo)
      (_bodyTarget : VExpr),
      Expr.ForallTelescope source
        (T.params.length + T.motives.length + minorIdx) suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take minorIdx) [])
        sourceDomain (T.minors[minorIdx]'hminor) ∧
      env.IsType Us.length
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
        (T.minors[minorIdx]'hminor) := by
  let domains := T.params ++
    (T.motives ++ (T.minors ++ (T.indices ++ T.major)))
  have hlength : domains.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length,
      T.major_length]
    omega
  have hposition : T.params.length + T.motives.length + minorIdx <
      numParams + numMotives + numMinors + numIndices + 1 := by
    rw [T.params_length, T.motives_length, ← T.minors_length] at *
    omega
  have htarget : target = VExpr.wrapForalls domains T.result := by
    simpa only [domains, List.append_assoc] using T.target_eq
  rcases T.typed.binderAt_target domains T.result htarget hlength
      (T.params.length + T.motives.length + minorIdx) hposition with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType, _Hbody⟩
  have htake : domains.take
      (T.params.length + T.motives.length + minorIdx) =
      T.params ++ T.motives ++ T.minors.take minorIdx := by
    change (T.params ++
      (T.motives ++ (T.minors ++ (T.indices ++ T.major)))).take
        (T.params.length + T.motives.length + minorIdx) = _
    rw [show T.params ++
        (T.motives ++ (T.minors ++ (T.indices ++ T.major))) =
      (T.params ++ T.motives) ++
        (T.minors ++ (T.indices ++ T.major)) by simp]
    rw [show T.params.length + T.motives.length + minorIdx =
      (T.params ++ T.motives).length + minorIdx by simp]
    rw [List.take_length_add_append]
    rw [List.take_append_of_le_length (Nat.le_of_lt hminor)]
  have hselected :
      domains[T.params.length + T.motives.length + minorIdx] =
        T.minors[minorIdx] := by
    simp only [domains]
    rw [List.getElem_append_right (by omega)]
    have hoffParams :
        T.params.length + T.motives.length + minorIdx - T.params.length =
          T.motives.length + minorIdx := by omega
    simp only [hoffParams]
    rw [List.getElem_append_right (by omega)]
    have hoffMotives :
        T.motives.length + minorIdx - T.motives.length = minorIdx := by omega
    simp only [hoffMotives]
    rw [List.getElem_append_left hminor]
  rw [htake, hselected] at Hdomain HdomainType
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType⟩

/-- Applying the parameter, motive, and minor prefix of a translated
recursor to its bound variables leaves exactly the index/major suffix.
This is the typed spine shared by every generated equation for the owner. -/
theorem RecursorTypeTelescope.prefixTyping
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered)
    (hfn : env.HasType Us.length [] fn target) :
    env.HasType Us.length
      (T.params ++ T.motives ++ T.minors).reverse
      (VExpr.mkApps (fn.liftN
        (T.params ++ T.motives ++ T.minors).length 0)
        (bvarSpine
          (T.params ++ T.motives ++ T.minors).length))
      (VExpr.wrapForalls (T.indices ++ T.major) T.result) := by
  have hfn' : env.HasType Us.length [] fn
      (VExpr.wrapForalls
        ((T.params ++ T.motives ++ T.minors) ++
          (T.indices ++ T.major)) T.result) := by
    rw [T.target_eq] at hfn
    simpa [List.append_assoc] using hfn
  have happ := VEnv.HasType.mkApps_wrapForalls_prefix_bvarSpine henv hfn'
  simpa [bvarSpine] using happ

/-- The common parameter/motive/minor prefix is itself a well-formed local
context, independently of the owner-specific index and major suffix. -/
theorem RecursorTypeTelescope.prefixContext
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered) :
    OnCtx (T.params ++ T.motives ++ T.minors).reverse
      (env.IsType Us.length) := by
  have htype := T.typed.isType
  change env.IsType Us.length [] target at htype
  rw [T.target_eq] at htype
  have htype' : env.IsType Us.length []
      (VExpr.wrapForalls
        (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major)
        T.result) := by
    simpa using htype
  have hgrouped : env.IsType Us.length []
      (VExpr.wrapForalls (T.params ++ T.motives ++ T.minors)
        (VExpr.wrapForalls (T.indices ++ T.major) T.result)) := by
    simpa [VExpr.wrapForalls_append, List.append_assoc] using htype'
  simpa using
    (VEnv.IsType.wrapForalls_inv henv (by trivial) hgrouped).1

/-- Opening the complete translated recursor telescope leaves a well-typed
residual in the five-group context.  This is the inversion premise
used to recover the dependency of the owner motive application on the
generated index/major suffix. -/
theorem RecursorTypeTelescope.fullContextResultType
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered) :
    let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
    OnCtx domains.reverse (env.IsType Us.length) ∧
      env.IsType Us.length domains.reverse T.result := by
  let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
  have htype := T.typed.isType
  change env.IsType Us.length [] target at htype
  rw [T.target_eq] at htype
  have htype' : env.IsType Us.length []
      (VExpr.wrapForalls domains T.result) := by
    simpa [domains] using htype
  have Hopened := VEnv.IsType.wrapForalls_inv henv (by trivial) htype'
  change OnCtx domains.reverse (env.IsType Us.length) ∧
    env.IsType Us.length domains.reverse T.result
  simpa only [List.append_nil] using Hopened

/-- The residual of any recursor-telescope translation is literally the owner
motive applied to the bound variables of the translated index and major suffix.
Stating this on `T` avoids choosing a second, possibly unrelated existential
translation when the result shape is used together with the owner-motive
telescope. -/
theorem RecursorTypeTelescope.resultShape
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < numMotives) :
    T.result = VExpr.mkApps
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (((List.range numIndices).reverse.map fun index =>
          .bvar (index + 1)) ++ [.bvar 0]) := by
  have htotal :
      numParams + numMotives + numMinors + numIndices + 1 ≤
        (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length := by
    simp only [List.length_append, T.params_length, T.motives_length,
      T.minors_length, T.indices_length, T.major_length]
    exact Nat.le_refl _
  exact TrExprS.concreteRecursorResult_eq howner htotal T.residual

/-- Lookup form before the owner index/major suffix is opened.  This is the
function typing used by the generic context inversion for bound-variable
applications. -/
theorem RecursorTypeTelescope.ownerMotiveOuterBvarTyping
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < T.motives.length) :
    let later := T.motives.drop (ownerIdx + 1) ++ T.minors
    let outer := T.params ++ T.motives ++ T.minors
    env.HasType Us.length outer.reverse (.bvar later.length)
      ((T.motives[ownerIdx]'howner).liftN (later.length + 1) 0) := by
  let later := T.motives.drop (ownerIdx + 1) ++ T.minors
  let older := (T.motives.take ownerIdx).reverse ++ T.params.reverse
  let outer := T.params ++ T.motives ++ T.minors
  have hsplit : T.motives = T.motives.take ownerIdx ++
      T.motives[ownerIdx] :: T.motives.drop (ownerIdx + 1) := by
    calc
      T.motives = T.motives.take (ownerIdx + 1) ++
          T.motives.drop (ownerIdx + 1) :=
        (List.take_append_drop (ownerIdx + 1) T.motives).symm
      _ = (T.motives.take ownerIdx ++ [T.motives[ownerIdx]]) ++
          T.motives.drop (ownerIdx + 1) := by
        rw [List.take_append_getElem howner]
      _ = T.motives.take ownerIdx ++ T.motives[ownerIdx] ::
          T.motives.drop (ownerIdx + 1) := by
        simp
  have hlookup : Lookup
      (later.reverse ++ T.motives[ownerIdx] :: older)
      later.length
      ((T.motives[ownerIdx]'howner).liftN (later.length + 1) 0) := by
    simpa [List.length_reverse] using
      Lookup.append_zero later.reverse (T.motives[ownerIdx]'howner) older
  have hmotivesReverse : T.motives.reverse =
      (T.motives.drop (ownerIdx + 1)).reverse ++
        T.motives[ownerIdx] :: (T.motives.take ownerIdx).reverse := by
    simp
  have hcontext : outer.reverse =
      later.reverse ++ T.motives[ownerIdx] :: older := by
    dsimp [outer, later, older]
    rw [List.reverse_append, List.reverse_append, hmotivesReverse]
    simp [List.append_assoc]
  apply VEnv.HasType.bvar
  rw [hcontext]
  exact hlookup

def RecursorTypeTelescope.mono
    (henv : env ≤ env')
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    RecursorTypeTelescope env' Us source target
      numParams numMotives numMinors numIndices ownerIdx where
  params := T.params
  motives := T.motives
  minors := T.minors
  indices := T.indices
  major := T.major
  result := T.result
  target_eq := T.target_eq
  params_length := T.params_length
  motives_length := T.motives_length
  minors_length := T.minors_length
  indices_length := T.indices_length
  major_length := T.major_length
  typed := T.typed.mono henv
  residual := T.residual.mono henv

/-- The translated `.recInfo` emitted by the executable determines the
five-group telescope. It is obtained solely by inverting the executable's
translation and the binder selections used by `declareRecursors`. -/
theorem GeneratedRecursorEntry.telescopeTranslation
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias) :
    Nonempty (RecursorTypeTelescope env H.info.levelParams
      H.info.type entry.2.type stats.params.size
      (recInfos.map (·.motive)).size (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx) := by
  have Htranslated : TrExprS env H.info.levelParams [] H.info.type
      entry.2.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using H.translated.1.2.2
  have HrawTelescope := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at HrawTelescope
  have Htelescope := HrawTelescope.inferImplicit_sameResidual (by rfl)
    1000 false
  rw [← H.type] at Htelescope
  have HtargetType : env.IsType H.info.levelParams.length [] entry.2.type :=
    TrExprS.isType_of_forallTelescope Htelescope (by omega) Htranslated
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope Htranslated HtargetType
  rcases TrExprS.forallTelescope_shape_with_context Htelescope Htranslated with
    ⟨domains, result, hdomainsLength, htarget, Hresult⟩
  rcases List.exists_append_five_of_length_eq domains stats.params.size
      (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size 1 hdomainsLength with
    ⟨params, motives, minors, indices, major, hdomains,
      hparams, hmotives, hminors, hindices, hmajor⟩
  refine ⟨⟨params, motives, minors, indices, major, result, ?_, hparams,
    hmotives, hminors, hindices, hmajor, Htyped, ?_⟩⟩
  · simpa [hdomains] using htarget
  · simpa [hdomains] using Hresult

/-- Pointwise five-group translation certificate for an entire generated
mutual recursor block. -/
def RecursorTypeTelescopes
    (env : VEnv) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) : Prop :=
  ∀ ownerIdx (hentry : ownerIdx < entries.length),
    ∃ info : RecursorVal,
      entries[ownerIdx].1 = .recInfo info ∧
      Nonempty (RecursorTypeTelescope env info.levelParams
        info.type entries[ownerIdx].2.type stats.params.size
        (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx)

theorem GeneratedRecursorEntry.rulesRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (hparams : nparams = stats.params.size) :
    ∀ rule ∈ H.info.rules, RestoreTelescope rule.rhs nparams := by
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hctor : i < indTypes[ownerIdx]!.ctors.length := by
    rw [← H.rules.length]
    exact hi
  rcases H.rules.entry i hctor hi with ⟨Hrule⟩
  exact Hrule.rhsRestoreTelescope hparams

theorem RestoreTelescope.instantiate1'
    (H : RestoreTelescope e n) (arg : Expr) (depth : Nat) :
    RestoreTelescope (e.instantiate1' arg depth) n := by
  induction H generalizing depth with
  | done => exact .done
  | forallE H ih =>
    simp only [Expr.instantiate1']
    exact .forallE (ih (depth + 1))
  | lam H ih =>
    simp only [Expr.instantiate1']
    exact .lam (ih (depth + 1))

theorem RestoreTelescope.instantiate1
    (H : RestoreTelescope e n) (arg : Expr) :
    RestoreTelescope (e.instantiate1 arg) n := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1' arg 0


end VerifyInductive
end Lean4Lean
