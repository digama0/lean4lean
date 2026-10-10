import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Inductive.Signature

namespace Lean4Lean

namespace VEnv

theorem addConstVal_mono
    {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁')
    (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  constructor
  · intro n a ha
    simp at ha ⊢
    split at ha <;> split <;> simp_all
    exact H.constants ha
  · exact H.defeqs
  · exact H.pats
  · exact H.projections

theorem addConstVals_mono
    {env₁ env₂ env₁' env₂' : VEnv} {cis : List VConstVal}
    (H : env₁ ≤ env₂)
    (h₁ : env₁.addConstVals cis = some env₁')
    (h₂ : env₂.addConstVals cis = some env₂') :
    env₁' ≤ env₂' := by
  induction cis generalizing env₁ env₂ env₁' env₂' with
  | nil =>
    simp [VEnv.addConstVals] at h₁ h₂
    subst env₁'
    subst env₂'
    exact H
  | cons ci cis ih =>
    simp only [VEnv.addConstVals] at h₁ h₂
    cases hhead₁ : env₁.addConst ci.name ci.toVConstant with
    | none => simp [hhead₁] at h₁
    | some middle₁ =>
      cases hhead₂ : env₂.addConst ci.name ci.toVConstant with
      | none => simp [hhead₂] at h₂
      | some middle₂ =>
        simp [hhead₁] at h₁
        simp [hhead₂] at h₂
        exact ih (addConstVal_mono H hhead₁ hhead₂) h₁ h₂

end VEnv

@[simp] theorem VExpr.getAppFnArgs_const :
    getAppFnArgs (.const name levels) = (.const name levels, []) := rfl

/-- Universe substitution commutes with exposing an application spine. -/
@[simp] theorem VExpr.getAppFnArgs_instL (e : VExpr) (levels : List VLevel) :
    (e.instL levels).getAppFnArgs =
      let (fn, args) := e.getAppFnArgs
      (fn.instL levels, args.map (VExpr.instL levels)) := by
  induction e with
  | app fn arg ihFn _ =>
    simp only [VExpr.instL, VExpr.getAppFnArgs_app, ihFn]
    simp
  | bvar | sort | const | proj | lam | forallE =>
    rfl

def VExpr.containsAnyConst (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const name _ => names.contains name
  | .proj typeName _ struct =>
    names.contains typeName || struct.containsAnyConst names
  | .app fn arg | .lam fn arg | .forallE fn arg =>
    fn.containsAnyConst names || arg.containsAnyConst names

/-- Universe substitution changes levels but not the constant-name support
of an expression. -/
@[simp] theorem VExpr.containsAnyConst_instL
    (e : VExpr) (levels : List VLevel) :
    (e.instL levels).containsAnyConst names = e.containsAnyConst names := by
  induction e <;> simp [VExpr.instL, VExpr.containsAnyConst, *]

theorem VExpr.containsAnyConst_mkApps_eq_false_iff
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).containsAnyConst names = false ↔
      fn.containsAnyConst names = false ∧
        ∀ arg ∈ args, arg.containsAnyConst names = false := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args by rfl, ih]
      simp [VExpr.containsAnyConst, and_assoc]

theorem VExpr.SourceConstFree.ofContainsAnyConst
    {expression : VExpr} {names : List Name}
    (H : expression.containsAnyConst names = false) :
    expression.SourceConstFree names := by
  induction expression with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | const name levels =>
    apply SourceConstFree.const name levels
    intro hname
    simp [VExpr.containsAnyConst, hname] at H
  | proj typeName index struct ihStruct =>
    rcases Bool.or_eq_false_iff.mp H with ⟨_, hstruct⟩
    exact .proj typeName index (ihStruct hstruct)
  | app fn arg ihFn ihArg =>
    rcases Bool.or_eq_false_iff.mp H with ⟨hfn, harg⟩
    exact .app (ihFn hfn) (ihArg harg)
  | lam domain body ihDomain ihBody | forallE domain body ihDomain ihBody =>
    rcases Bool.or_eq_false_iff.mp H with ⟨hdomain, hbody⟩
    first | exact .lam (ihDomain hdomain) (ihBody hbody)
          | exact .forallE (ihDomain hdomain) (ihBody hbody)

/-- Universe instantiation preserves source support. -/
theorem VExpr.SourceConstFree.instL
    {expression : VExpr} {names : List Name}
    (H : expression.SourceConstFree names) (levels : List VLevel) :
    (expression.instL levels).SourceConstFree names := by
  induction H with
  | bvar index => exact .bvar index
  | sort level => exact .sort _
  | const name sourceLevels fresh => exact .const name _ fresh
  | proj typeName index _ ihStruct => exact .proj typeName index ihStruct
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody

/-- Bound-variable weakening preserves source support. -/
theorem VExpr.SourceConstFree.liftN
    {expression : VExpr} {names : List Name}
    (H : expression.SourceConstFree names) (n k : Nat) :
    (expression.liftN n k).SourceConstFree names := by
  induction H generalizing k with
  | bvar index => exact .bvar _
  | sort level => exact .sort level
  | const name sourceLevels fresh => exact .const name sourceLevels fresh
  | proj typeName index _ ihStruct => exact .proj typeName index (ihStruct k)
  | app _ _ ihFn ihArg => exact .app (ihFn k) (ihArg k)
  | lam _ _ ihDomain ihBody => exact .lam (ihDomain k) (ihBody (k + 1))
  | forallE _ _ ihDomain ihBody =>
    exact .forallE (ihDomain k) (ihBody (k + 1))


theorem VInductDecl.ValidIndAppAt.forgetTarget
    {decl : VInductDecl} {target : Option Name}
    {depth : Nat} {e : VExpr}
    (H : decl.ValidIndAppAt target depth e) :
    decl.ValidIndAppAt none depth e := by
  rcases H with ⟨type, htype, _htarget, levels, hfn, hlevels,
    hargs, hparams, hindices⟩
  exact ⟨type, htype, Or.inl rfl, levels, hfn, hlevels,
    hargs, hparams, hindices⟩

/-- Instantiating universes preserves the syntactic recursive-application
criterion.  In particular this lets a recursive domain checked under a fresh
recursor universe be specialized back to the declaration universe arity. -/
theorem VInductDecl.ValidIndAppAt.instL
    {decl : VInductDecl} {target : Option Name}
    {depth : Nat} {e : VExpr} (levels : List VLevel)
    (H : decl.ValidIndAppAt target depth e) :
    decl.ValidIndAppAt target depth (e.instL levels) := by
  unfold VInductDecl.ValidIndAppAt at H ⊢
  generalize hspine : e.getAppFnArgs = spine at H
  rcases spine with ⟨fn, args⟩
  rw [VExpr.getAppFnArgs_instL, hspine]
  rcases H with ⟨type, htype, htarget, sourceLevels, hfn,
    hlevelLength, hargLength, hparams, hindices⟩
  refine ⟨type, htype, htarget, sourceLevels.map (VLevel.inst levels),
    ?_, by simpa using hlevelLength, by simpa using hargLength, ?_, ?_⟩
  · simp [hfn, VExpr.instL]
  · rw [← List.map_take, hparams]
    simp [VInductDecl.paramVars, VExpr.instL]
  · intro arg harg
    rw [← List.map_drop] at harg
    rcases List.mem_map.mp harg with ⟨source, hsource, rfl⟩
    exact (hindices source hsource).instL levels

theorem VInductDecl.RawIndAppAt.instL
    {decl : VInductDecl} {target : Option Name}
    {depth : Nat} {e : VExpr} (levels : List VLevel)
    (H : decl.RawIndAppAt target depth e) :
    decl.RawIndAppAt target depth (e.instL levels) := by
  unfold VInductDecl.RawIndAppAt at H ⊢
  generalize hspine : e.getAppFnArgs = spine at H
  rcases spine with ⟨fn, args⟩
  rw [VExpr.getAppFnArgs_instL, hspine]
  rcases H with ⟨type, htype, htarget, sourceLevels, hfn,
    hlevelLength, hargLength, hparams⟩
  refine ⟨type, htype, htarget, sourceLevels.map (VLevel.inst levels),
    ?_, by simpa using hlevelLength, by simpa using hargLength, ?_⟩
  · simp [hfn, VExpr.instL]
  · rw [← List.map_take, hparams]
    simp [VInductDecl.paramVars, VExpr.instL]

/- Positivity is recursively modulo definitional equality: the executable
checker exposes every higher-order body to WHNF, not only the outermost field
type.  `SyntacticallyPositive` classifies one exposed head, while `Positive`
records the definitional-equality step and recurs under `forallE`. -/
namespace VInductDecl

mutual

/-- Positivity modulo one WHNF/definitional-equality step. -/
inductive Positive (env : VEnv) (decl : VInductDecl) :
    List VExpr → Nat → VExpr → Prop
  | unfold :
    env.IsDefEq decl.uvars ctx e exposed type →
    SyntacticallyPositive env decl ctx depth exposed →
    Positive env decl ctx depth e
/-- The exposed-head cases of strict positivity. -/
inductive SyntacticallyPositive (env : VEnv)
    (decl : VInductDecl) : List VExpr → Nat → VExpr → Prop
  | nonrecursive :
    e.SourceConstFree (decl.types.map (·.name)) →
    SyntacticallyPositive env decl ctx depth e
  | forallE :
    dom.SourceConstFree (decl.types.map (·.name)) →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    Positive env decl (checkedDom :: ctx) (depth + 1) checkedBody →
    SyntacticallyPositive env decl ctx depth (.forallE dom body)
  | recursive :
    decl.ValidIndAppAt none depth e →
    SyntacticallyPositive env decl ctx depth e

end

end VInductDecl

/-- A constructor field for which recursor generation must introduce an
induction hypothesis. Unlike positivity, this judgment follows higher-order
binders only to classify the field's eventual result; positivity of the whole
domain is checked separately by `Positive`. -/
inductive VInductDecl.RecursiveArg (env : VEnv) (decl : VInductDecl) :
    List VExpr → Nat → VExpr → Prop
  | direct :
    env.IsDefEq decl.uvars ctx e exposed type →
    decl.ValidIndAppAt none depth exposed →
    decl.RecursiveArg env ctx depth e
  | forallE :
    env.IsDefEq decl.uvars ctx e (.forallE dom body) type →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    decl.RecursiveArg env (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.RecursiveArg env ctx depth e

/-- Target-preserving recursive-argument classification.  The executable
classifier returns a mutual-family index; this judgment carries the matching
family name through every higher-order binder instead of forgetting it at the
direct application. -/
inductive VInductDecl.RecursiveArgAtTarget
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) (target : Name) :
    List VExpr → Nat → VExpr → Prop
  | direct :
    env.IsDefEq uvars ctx e exposed type →
    decl.ValidIndAppAt (some target) depth exposed →
    decl.RecursiveArgAtTarget env uvars target ctx depth e
  | forallE :
    env.IsDefEq uvars ctx e (.forallE dom body) type →
    env.IsDefEq uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq uvars (dom :: ctx) body checkedBody bodyType →
    decl.RecursiveArgAtTarget env uvars target
      (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.RecursiveArgAtTarget env uvars target ctx depth e

/-- Recursive-argument classification is stable under arbitrary universe
specialization.  The context and classified domain are instantiated in
lockstep with every definitional-equality premise. -/
theorem VInductDecl.RecursiveArgAtTarget.instL
    {decl : VInductDecl} {env : VEnv} {uvars targetUvars : Nat}
    {target : Name} {ctx : List VExpr} {depth : Nat} {e : VExpr}
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF targetUvars)
    (H : decl.RecursiveArgAtTarget env uvars target ctx depth e) :
    decl.RecursiveArgAtTarget env targetUvars target
      (ctx.map (VExpr.instL levels)) depth (e.instL levels) := by
  induction H with
  | direct hdef happ =>
    exact .direct (hdef.instL hlevels) (happ.instL levels)
  | forallE he hdom hbody _ ih =>
    simpa [VExpr.instL] using
      VInductDecl.RecursiveArgAtTarget.forallE
        (he.instL hlevels) (hdom.instL hlevels)
        (hbody.instL hlevels) ih

/-- Constructor fields followed by the constructor's target application. -/
inductive VInductDecl.CtorTailWF (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) : List VExpr → Nat → VExpr → Prop
  | result :
    decl.ValidIndAppAt (some target.name) depth result' →
    env.IsDefEq decl.uvars ctx result result' type →
    decl.CtorTailWF env target ctx depth result
  | field :
    env.HasType decl.uvars ctx dom (.sort fieldLevel) →
    (target.resultLevel ≈ .zero ∨ fieldLevel ≤ target.resultLevel) →
    (decl.isUnsafe = true ∨ decl.Positive env ctx depth dom) →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort checkedLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    decl.CtorTailWF env target (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.CtorTailWF env target ctx depth (.forallE dom body)

theorem VInductDecl.ParamsDefEq.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.ParamsDefEq env params params') :
    decl.ParamsDefEq env' params params' :=
  VEnv.IsDefEqCtx.mono henv H

theorem VInductDecl.Positive.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.Positive env ctx depth e) :
    decl.Positive env' ctx depth e := by
  exact VInductDecl.Positive.rec
    (motive_1 := fun ctx depth e _ => decl.Positive env' ctx depth e)
    (motive_2 := fun ctx depth e _ =>
      decl.SyntacticallyPositive env' ctx depth e)
    (fun hdef _ ih => .unfold (hdef.mono henv) ih)
    (fun h => .nonrecursive h)
    (fun hcontains hdom hbody _ ih =>
      .forallE hcontains (hdom.mono henv) (hbody.mono henv) ih)
    (fun h => .recursive h) H

theorem VInductDecl.RecursiveArg.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.RecursiveArg env ctx depth e) :
    decl.RecursiveArg env' ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct (hdef.mono henv) happ
  | forallE he hdom hbody _ ih =>
    exact .forallE (he.mono henv) (hdom.mono henv) (hbody.mono henv) ih

theorem VInductDecl.CtorTailWF.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorTailWF env target ctx depth e) :
    decl.CtorTailWF env' target ctx depth e := by
  induction H with
  | result happ hdef => exact .result happ (hdef.mono henv)
  | field htype hlevel hpositive hdom hbody _ ih =>
    exact .field (htype.mono henv) hlevel
      (hpositive.elim (fun h => .inl h)
        (fun h => .inr (h.mono henv)))
      (hdom.mono henv) (hbody.mono henv) ih

def VInductDecl.CtorShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) (ctor : VConstVal) : Prop :=
  ∃ normalized ownParams tail exprType tailCtx,
    env.IsDefEq decl.uvars [] ctor.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams ∧
    env.IsDefEqCtx decl.uvars [] ownParams.reverse tailCtx ∧
    decl.CtorTailWF env target tailCtx 0 tail

theorem VInductDecl.TypeShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.TypeShape env params type) :
    decl.TypeShape env' params type := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      htype, hparams, hindices, hparamsDefEq, hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    htype.mono henv, hparams, hindices, hparamsDefEq.mono henv,
    hresult.mono henv⟩

/-- A header of the recorded shape is definitionally a telescope, of the
recorded parameter and index arity, whose body is definitionally the recorded
sort in the telescope's own scope.  This open form needs no well-formedness
of the environment. -/
theorem VInductDecl.TypeShape.header
    {env : VEnv} {decl : VInductDecl} {params : List VExpr} {type : VInductiveType}
    (H : decl.TypeShape env params type) :
    ∃ domains body exprType,
      domains.length = decl.nparams + type.numIndices ∧
      env.IsDefEq decl.uvars [] type.type (VExpr.wrapForalls domains body) exprType ∧
      env.IsDefEq decl.uvars domains.reverse body
        (.sort type.resultLevel) (.sort (.succ type.resultLevel)) := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      htype, hparams, hindices, _, hresult⟩
  have h1 := VExpr.takeForalls_eq_wrapForalls hparams
  have h2 := VExpr.takeForalls_eq_wrapForalls hindices
  refine ⟨ownParams ++ indices, result, exprType, by simp [h1.2, h2.2], ?_, ?_⟩
  · have : normalized = VExpr.wrapForalls (ownParams ++ indices) result := by
      rw [h1.1, h2.1]
      simp [VExpr.wrapForalls]
    exact this ▸ htype
  · simpa [List.reverse_append] using hresult

theorem VInductDecl.CtorShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorShape env params target ctor) :
    decl.CtorShape env' params target ctor := by
  rcases H with
    ⟨normalized, ownParams, tail, exprType, tailCtx, htype, hparams,
      hparamsDefEq, hctx, htail⟩
  exact ⟨normalized, ownParams, tail, exprType, tailCtx, htype.mono henv,
    hparams, hparamsDefEq.mono henv, hctx.mono henv, htail.mono henv⟩

theorem VInductDecl.CtorParameterShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorParameterShape env params ctor) :
    decl.CtorParameterShape env' params ctor := by
  rcases H with ⟨ownParams, tail, htake, hparams⟩
  exact ⟨ownParams, tail, htake, hparams.mono henv⟩

/-! ## Abstract nested expansion

Nested lowering preserves the position of every constructor field, replacing
maximal nested applications by applications of fresh auxiliary families. The
relations below state that source-to-expanded correspondence independently of
the executable lowering state; the refinement proof shows that the stateful `Expr`
traversal of lowering projects to them (section 3.3 of the design notes). -/

/-- Structural expression expansion with an explicit relation `leaf` for maximal
nested occurrences (`.occurrence`). Binder depth is retained because direct inductive
applications use depth-indexed parameter variables. -/
inductive VExpr.NestedExprExpansion
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → VExpr → VExpr → Prop
  | occurrence : leaf depth source target →
      NestedExprExpansion leaf depth source target
  | bvar : NestedExprExpansion leaf depth (.bvar index) (.bvar index)
  | sort : NestedExprExpansion leaf depth (.sort level) (.sort level)
  | const : NestedExprExpansion leaf depth (.const name levels)
      (.const name levels)
  | proj : NestedExprExpansion leaf depth source target →
      NestedExprExpansion leaf depth (.proj typeName index source)
        (.proj typeName index target)
  | app : NestedExprExpansion leaf depth sourceFn targetFn →
      NestedExprExpansion leaf depth sourceArg targetArg →
      NestedExprExpansion leaf depth (.app sourceFn sourceArg)
        (.app targetFn targetArg)
  | lam : NestedExprExpansion leaf depth sourceDomain targetDomain →
      NestedExprExpansion leaf (depth + 1) sourceBody targetBody →
      NestedExprExpansion leaf depth (.lam sourceDomain sourceBody)
        (.lam targetDomain targetBody)
  | forallE : NestedExprExpansion leaf depth sourceDomain targetDomain →
      NestedExprExpansion leaf (depth + 1) sourceBody targetBody →
      NestedExprExpansion leaf depth (.forallE sourceDomain sourceBody)
        (.forallE targetDomain targetBody)

/-- Change only the interpretation of successful leaves. -/
theorem VExpr.NestedExprExpansion.map
    (Hleaf : ∀ {depth source target}, leaf depth source target →
      leaf' depth source target)
    (H : VExpr.NestedExprExpansion leaf depth source target) :
    VExpr.NestedExprExpansion leaf' depth source target := by
  induction H with
  | occurrence h => exact .occurrence (Hleaf h)
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | proj _ ihSource => exact .proj ihSource
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody

/-- Leaving an abstract expression unchanged is always an expansion. -/
theorem VExpr.NestedExprExpansion.refl
    (leaf : Nat → VExpr → VExpr → Prop)
    (depth : Nat) (e : VExpr) :
    VExpr.NestedExprExpansion leaf depth e e := by
  induction e generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | proj _ _ _ ihSource => exact .proj (ihSource depth)
  | app _ _ ihFn ihArg => exact .app (ihFn depth) (ihArg depth)
  | lam _ _ ihDomain ihBody =>
    exact .lam (ihDomain depth) (ihBody (depth + 1))
  | forallE _ _ ihDomain ihBody =>
    exact .forallE (ihDomain depth) (ihBody (depth + 1))

/-- The exact common-parameter prefix retained by nested lowering.  Unlike
`NestedExprExpansion` of the complete constructor, this records where each
of the first `arity` forall domains sits in the depth-indexed expansion. -/
inductive VExpr.NestedForallPrefixExpansion
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VExpr.NestedExprExpansion leaf depth sourceBody targetBody) :
      VExpr.NestedForallPrefixExpansion leaf depth 0 sourceBody targetBody
  | cons
      (Hdomain : VExpr.NestedExprExpansion leaf depth
        sourceDomain targetDomain)
      (Hbody : VExpr.NestedForallPrefixExpansion leaf (depth + 1) arity
        sourceBody targetBody) :
      VExpr.NestedForallPrefixExpansion leaf depth (arity + 1)
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)

/-- A forall-prefix expansion is in particular an expansion of the whole
expressions: the prefix relation already expands the remaining body. -/
theorem VExpr.NestedForallPrefixExpansion.toNestedExprExpansion
    {leaf : Nat → VExpr → VExpr → Prop} {depth arity : Nat} {source target : VExpr}
    (H : VExpr.NestedForallPrefixExpansion leaf depth arity source target) :
    VExpr.NestedExprExpansion leaf depth source target := by
  induction H with
  | nil Hbody => exact Hbody
  | cons Hdomain _ ih => exact .forallE Hdomain ih

/-- One positionally corresponding source/expanded constructor.  The common
parameter prefix also expands the remaining body, so the whole type expansion
follows (`NestedForallPrefixExpansion.toNestedExprExpansion`). -/
structure VInductDecl.NestedConstructorExpansion
    (leaf : Nat → VExpr → VExpr → Prop) (nparams : Nat)
    (source target : VConstVal) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  parameters : VExpr.NestedForallPrefixExpansion leaf 0 nparams
    source.type target.type

/-- The whole constructor type expands. -/
theorem VInductDecl.NestedConstructorExpansion.type
    {leaf : Nat → VExpr → VExpr → Prop} {nparams : Nat} {source target : VConstVal}
    (H : VInductDecl.NestedConstructorExpansion leaf nparams source target) :
    VExpr.NestedExprExpansion leaf 0 source.type target.type :=
  H.parameters.toNestedExprExpansion

/-- One source family and its positionally corresponding expanded family.
Headers are compared semantically; constructor bodies retain the structural
nested-expansion relation. -/
structure VInductDecl.NestedTypeExpansion
    (env : VEnv) (decl : VInductDecl)
    (leaf : Nat → VExpr → VExpr → Prop)
    (source target : VInductiveType) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  type : env.IsDefEqU decl.uvars [] source.type target.type
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel
  constructors : List.Forall₂ (NestedConstructorExpansion leaf decl.nparams)
    source.ctors target.ctors

/-! ### Raw constructor shape across nested expansion -/

@[simp] theorem VExpr.getAppFnArgs_bvar :
    getAppFnArgs (.bvar index) = (.bvar index, []) := rfl
@[simp] theorem VExpr.getAppFnArgs_sort :
    getAppFnArgs (.sort level) = (.sort level, []) := rfl
@[simp] theorem VExpr.getAppFnArgs_lam :
    getAppFnArgs (.lam domain body) = (.lam domain body, []) := rfl
@[simp] theorem VExpr.getAppFnArgs_forallE :
    getAppFnArgs (.forallE domain body) = (.forallE domain body, []) := rfl
@[simp] theorem VExpr.getAppFnArgs_proj :
    getAppFnArgs (.proj typeName index struct) =
      (.proj typeName index struct, []) := rfl

/-- A constant-free expression cannot be headed by an excluded constant. -/
theorem VExpr.SourceConstFree.head_not_mem
    (H : VExpr.SourceConstFree names e)
    (hhead : e.getAppFnArgs = (.const name levels, args)) : name ∉ names := by
  induction H generalizing args with
  | bvar index => simp at hhead
  | sort level => simp at hhead
  | const name' levels' fresh =>
    simp only [VExpr.getAppFnArgs_const, Prod.mk.injEq, VExpr.const.injEq] at hhead
    rw [← hhead.1.1]
    exact fresh
  | proj typeName index _ _ => simp at hhead
  | app _ _ ihFn _ =>
    simp only [VExpr.getAppFnArgs_app] at hhead
    obtain ⟨hfn, _⟩ := Prod.mk.inj hhead
    exact ihFn (Prod.ext hfn rfl)
  | lam _ _ _ _ => simp at hhead
  | forallE _ _ _ _ => simp at hhead

/-- Members of a list with pairwise distinct images agree once their images
agree. -/
theorem List.eq_of_mem_of_nodup_map {α β : Type _} {f : α → β} {l : List α}
    (hnodup : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hf : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hf.symm⟩ hnodup.1
    · exact absurd ⟨a, ha, hf⟩ hnodup.1
    · exact ih hnodup.2 ha hb

/-- An expansion whose target avoids every leaf head constant is the identity:
each leaf replaces a source expression by an application headed by one of the
excluded constants. -/
theorem VExpr.NestedExprExpansion.eq_of_sourceConstFree
    {leaf : Nat → VExpr → VExpr → Prop} {names : List Name}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      ∃ name ∈ names, ∃ levels args,
        output.getAppFnArgs = (.const name levels, args))
    (H : VExpr.NestedExprExpansion leaf depth source target)
    (hfree : VExpr.SourceConstFree names target) : source = target := by
  induction H with
  | occurrence h =>
    rcases hleaf h with ⟨name, hname, levels, args, hhead⟩
    exact absurd hname (hfree.head_not_mem hhead)
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | proj _ ih =>
    cases hfree with
    | proj _ _ h => rw [ih h]
  | app _ _ ihFn ihArg =>
    cases hfree with
    | app hfn harg => rw [ihFn hfn, ihArg harg]
  | lam _ _ ihDomain ihBody =>
    cases hfree with
    | lam hdomain hbody => rw [ihDomain hdomain, ihBody hbody]
  | forallE _ _ ihDomain ihBody =>
    cases hfree with
    | forallE hdomain hbody => rw [ihDomain hdomain, ihBody hbody]

/-- Leaves are applications, so a forall telescope on the expanded side is
matched binder by binder on the source side. -/
theorem VExpr.NestedExprExpansion.wrapForalls_inv
    {leaf : Nat → VExpr → VExpr → Prop}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      ∃ name levels args, output.getAppFnArgs = (.const name levels, args))
    (H : VExpr.NestedExprExpansion leaf depth source
      (VExpr.wrapForalls doms result)) :
    ∃ doms' result', source = VExpr.wrapForalls doms' result' ∧
      doms'.length = doms.length ∧
      VExpr.NestedExprExpansion leaf (depth + doms.length) result' result := by
  induction doms generalizing depth source with
  | nil => exact ⟨[], source, rfl, rfl, by simpa [VExpr.wrapForalls] using H⟩
  | cons dom doms ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at H
    cases H with
    | occurrence h =>
      rcases hleaf h with ⟨name, levels, args, hhead⟩
      simp at hhead
    | forallE Hdomain Hbody =>
      rename_i sourceDomain sourceBody
      rcases ih Hbody with ⟨doms', result', hsource, hlength, Hresult⟩
      refine ⟨sourceDomain :: doms', result', ?_, ?_, ?_⟩
      · simp [VExpr.wrapForalls, hsource]
      · simp [hlength]
      · have : depth + (dom :: doms).length = depth + 1 + doms.length := by
          simp only [List.length_cons]
          omega
        rw [this]
        exact Hresult

@[simp] theorem VExpr.forallArity_wrapForalls
    (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls domains body).forallArity =
      domains.length + body.forallArity := by
  induction domains with
  | nil => simp [wrapForalls]
  | cons dom domains ih =>
    simp [wrapForalls, VExpr.forallArity] at ih ⊢
    omega


theorem List.Forall₂.getElem_of {α β : Type _} {R : α → β → Prop}
    {as : List α} {bs : List β} (H : List.Forall₂ R as bs) (i : Nat)
    (ha : i < as.length) (hb : i < bs.length) : R as[i] bs[i] := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i (by simpa using ha) (by simpa using hb)

/-- A leaf cannot alter an application spine headed by a constant `name` that heads no leaf
output. Arguments remain related; their syntax need not be equal. -/
theorem VExpr.NestedExprExpansion.const_spine_inv
    {leaf : Nat → VExpr → VExpr → Prop}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      ∀ levels, output.getAppFnArgs.1 ≠ .const name levels)
    (H : VExpr.NestedExprExpansion leaf depth source target)
    (hhead : target.getAppFnArgs.1 = .const name levels) :
    source.getAppFnArgs.1 = .const name levels ∧
      List.Forall₂ (VExpr.NestedExprExpansion leaf depth)
        source.getAppFnArgs.2 target.getAppFnArgs.2 := by
  induction H with
  | occurrence h => exact (hleaf h _ hhead).elim
  | const => exact ⟨hhead, .nil⟩
  | @app d sf tf sa ta hfn harg ihfn _ =>
    simp only [VExpr.getAppFnArgs_app] at hhead ⊢
    have ⟨hf, hargs⟩ := ihfn hhead
    refine ⟨hf, ?_⟩
    have happ : ∀ {as bs}, List.Forall₂ (NestedExprExpansion leaf d) as bs →
        List.Forall₂ (NestedExprExpansion leaf d)
          (as ++ [sa]) (bs ++ [ta]) := by
      intro as bs h
      induction h with
      | nil => exact .cons harg .nil
      | cons h _ ih => exact .cons h ih
    exact happ hargs
  | bvar | sort | proj | lam | forallE => cases hhead

/-- The source declaration's constructors inherit the raw syntactic shape of
their positionally corresponding expanded constructors: nested lowering only
rewrites maximal nested applications inside binder domains, never the forall
telescope or the constant-headed result application itself. -/
theorem VInductDecl.RawCtorShape.ofNestedExpansion_core
    {leaf : Nat → VExpr → VExpr → Prop} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      ∃ auxiliary ∈ generated, ∃ levels args,
        output.getAppFnArgs = (.const auxiliary.name levels, args))
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name))
    (hnodup : (expanded.types.map (·.name)).Nodup)
    {sourceType targetType : VInductiveType}
    (hsourceMem : sourceType ∈ source.types)
    (htargetMem : targetType ∈ expanded.types)
    (hname : targetType.name = sourceType.name)
    (hindices : targetType.numIndices = sourceType.numIndices)
    {sourceCtor targetCtor : VConstVal}
    (Hexp : VExpr.NestedExprExpansion leaf 0 sourceCtor.type targetCtor.type)
    (Hraw : expanded.RawCtorShape targetType targetCtor) :
    source.RawCtorShape sourceType sourceCtor ∧
      sourceCtor.type.forallArity = targetCtor.type.forallArity := by
  rcases Hraw with ⟨doms, result, hwrap, hle, hvalid, hhead⟩
  rw [hwrap] at Hexp
  rcases Hexp.wrapForalls_inv (fun h => by
      rcases hleaf h with ⟨auxiliary, _, levels, args, hhead⟩
      exact ⟨auxiliary.name, levels, args, hhead⟩) with
    ⟨doms', result', hsource, hlength, Hresult⟩
  have hsourceNotGenerated : sourceType.name ∉ generated.map (·.name) := by
    intro hmem
    rw [hnames, List.map_append] at hnodup
    exact (List.nodup_append.mp hnodup).2.2 _ (List.mem_map_of_mem hsourceMem) _ hmem rfl
  obtain ⟨type, htype, hnameEq, levels, hfn, hlevels, hargs, hparams⟩ := hvalid
  have htypeName : type.name = sourceType.name := by
    rcases hnameEq with h | h
    · cases h
    · rw [← hname]
      exact (Option.some.inj h).symm
  have htypeEq : type = targetType :=
    List.eq_of_mem_of_nodup_map hnodup htype htargetMem (htypeName.trans hname.symm)
  subst htypeEq
  change result.getAppFnArgs.2.length = expanded.nparams + type.numIndices at hargs
  change result.getAppFnArgs.2.take expanded.nparams =
    expanded.paramVars (doms.length - expanded.nparams) at hparams
  have hleafNames : ∀ {depth input output}, leaf depth input output →
      ∃ name ∈ generated.map (·.name), ∃ levels args,
        output.getAppFnArgs = (.const name levels, args) := by
    intro depth input output h
    rcases hleaf h with ⟨auxiliary, hauxiliary, levels, args, hhead⟩
    exact ⟨auxiliary.name, List.mem_map_of_mem hauxiliary, levels, args, hhead⟩
  have hnohead : ∀ {depth input output}, leaf depth input output →
      ∀ levels, output.getAppFnArgs.1 ≠ .const sourceType.name levels := by
    intro depth input output h levels heq
    rcases hleafNames h with ⟨name, hmem, ls, args, hspine⟩
    rw [hspine] at heq
    have hn := (VExpr.const.inj heq).1
    exact hsourceNotGenerated (hn ▸ hmem)
  have hhead' : result.getAppFnArgs.1 =
      .const sourceType.name (VLevel.params expanded.uvars) := by simpa [hname] using hhead
  have ⟨hsourceHead, hrelation⟩ := Hresult.const_spine_inv hnohead hhead' 
  have hrelLength : result'.getAppFnArgs.2.length = result.getAppFnArgs.2.length := by
    have hl : ∀ {as bs : List VExpr}, List.Forall₂ (VExpr.NestedExprExpansion leaf (0 + doms.length)) as bs →
        as.length = bs.length := by
      intro as bs h
      induction h with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    exact hl hrelation
  have hparamsEq : result'.getAppFnArgs.2.take expanded.nparams =
      result.getAppFnArgs.2.take expanded.nparams := by
    apply List.ext_getElem
    · simp [hrelLength]
    · intro i hi hi'
      have hiTarget : i < result.getAppFnArgs.2.length := by
        simp only [List.length_take] at hi'
        omega
      have hiSource : i < result'.getAppFnArgs.2.length := by
        rw [hrelLength]
        exact hiTarget
      have hentry := List.Forall₂.getElem_of hrelation i hiSource hiTarget
      have hfree : (result.getAppFnArgs.2[i]).SourceConstFree
          (generated.map (·.name)) := by
        have hmem := List.getElem_mem (l := result.getAppFnArgs.2.take expanded.nparams) hi'
        simp only [List.getElem_take] at hmem
        change (result.getAppFnArgs.2[i]'hiTarget) ∈ result.getAppFnArgs.2.take expanded.nparams at hmem
        rw [hparams] at hmem
        simp only [VInductDecl.paramVars, List.mem_map] at hmem
        obtain ⟨j, _, heq⟩ := hmem
        rw [← heq]
        exact .bvar _
      simpa only [List.getElem_take] using hentry.eq_of_sourceConstFree hleafNames hfree
  refine ⟨⟨doms', result', hsource, by rw [hlength]; exact hnparams ▸ hle, ?_, ?_⟩, ?_⟩
  · refine ⟨sourceType, hsourceMem, Or.inr rfl, VLevel.params expanded.uvars,
      hsourceHead, by simp [huvars], ?_, ?_⟩
    · change result'.getAppFnArgs.2.length = _
      rw [hrelLength, hargs, hnparams, hindices]
    · rw [← hnparams]
      change result'.getAppFnArgs.2.take expanded.nparams = _
      rw [hparamsEq, hparams]
      simp [VInductDecl.paramVars, hnparams, hlength]
  · simpa [huvars] using hsourceHead
  · rw [hsource, hwrap, VExpr.forallArity_wrapForalls, VExpr.forallArity_wrapForalls, hlength]
    have hs : result'.forallArity = 0 := by cases result' <;> first | rfl | cases hsourceHead
    have ht : result.forallArity = 0 := by cases result <;> first | rfl | cases hhead
    rw [hs, ht]


theorem VInductDecl.RawCtorShape.ofNestedExpansion
    {leaf : Nat → VExpr → VExpr → Prop} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (hleaf : ∀ {depth input output}, leaf depth input output →
      ∃ auxiliary ∈ generated, ∃ levels args,
        output.getAppFnArgs = (.const auxiliary.name levels, args))
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name))
    (hnodup : (expanded.types.map (·.name)).Nodup)
    {sourceType targetType : VInductiveType}
    (hsourceMem : sourceType ∈ source.types)
    (htargetMem : targetType ∈ expanded.types)
    (hname : targetType.name = sourceType.name)
    (hindices : targetType.numIndices = sourceType.numIndices)
    {sourceCtor targetCtor : VConstVal}
    (Hexp : VExpr.NestedExprExpansion leaf 0 sourceCtor.type targetCtor.type)
    (Hraw : expanded.RawCtorShape targetType targetCtor) :
    source.RawCtorShape sourceType sourceCtor :=
  (VInductDecl.RawCtorShape.ofNestedExpansion_core hleaf huvars hnparams hnames
    hnodup hsourceMem htargetMem hname hindices Hexp Hraw).1

/-- Positional agreement of constructor telescope lengths between a source
declaration and its nested expansion. -/
def VInductDecl.ConstructorArityPrefix (source expanded : VInductDecl) : Prop :=
  ∀ (familyIdx : Nat) (hsource : familyIdx < source.types.length)
    (hexpanded : familyIdx < expanded.types.length)
    (ctorIdx : Nat) (hsourceCtor : ctorIdx < source.types[familyIdx].ctors.length)
    (hexpandedCtor : ctorIdx < expanded.types[familyIdx].ctors.length),
    (source.types[familyIdx].ctors[ctorIdx]).type.forallArity =
      (expanded.types[familyIdx].ctors[ctorIdx]).type.forallArity


/-- Source-level obligations that cannot be erased by ordinary or nested
compilation. In particular constructor types are checked in an environment
containing all mutually declared headers, before any nested occurrence is
lowered. -/
def VInductDecl.SourceWF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.types ≠ [] ∧
  decl.sourceNames.Nodup ∧
  (∀ type ∈ decl.types, type.uvars = decl.uvars) ∧
  (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) ∧
  ∃ envTypes envCtors,
    env.addConstVals decl.typeConstants = some envTypes ∧
    envTypes.addConstVals decl.constructorConstants = some envCtors ∧
    (∀ type ∈ decl.types, type.toVConstant.WF env) ∧
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes

theorem VInductDecl.SourceWF.mono_of_addConstVals {decl : VInductDecl} {env env' envTypes envCtors : VEnv}
    (H : decl.SourceWF env) (hle : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors) :
    decl.SourceWF env' := by
  rcases H with ⟨hnonempty, hnames, htypeUvars, hctorUvars, sourceTypes, sourceCtors,
    hsourceTypes, _, hsourceTypesWF, hsourceCtorsWF⟩
  have hsourceTypesLE : sourceTypes ≤ envTypes :=
    VEnv.addConstVals_mono hle hsourceTypes htypes
  exact ⟨hnonempty, hnames, htypeUvars, hctorUvars, envTypes, envCtors, htypes, hctors,
    fun type htype => (hsourceTypesWF type htype).mono hle,
    fun ctor hctor => (hsourceCtorsWF ctor hctor).mono hsourceTypesLE⟩

/-- Formation conditions for ordinary and mutually recursive inductive blocks.
Nested declarations use the same source judgment; their lowering must later
produce these conditions for the expanded mutual family. -/
def VInductDecl.OrdinaryFormationWF (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ params resultLevel envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types,
      type.resultLevel ≈ resultLevel ∧ decl.TypeShape env params type) ∧
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorParameterShape envTypes params ctor ∧
      decl.CtorShape envTypes params type ctor) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor

theorem VInductDecl.OrdinaryFormationWF.mono_of_addConstVals {decl : VInductDecl} {env env' envTypes : VEnv}
    (H : decl.OrdinaryFormationWF env) (hle : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes) :
    decl.OrdinaryFormationWF env' := by
  rcases H with ⟨params, resultLevel, formationTypes, hformationTypes, htypeShapes,
    hctorShapes, hraw⟩
  have hformationTypesLE : formationTypes ≤ envTypes :=
    VEnv.addConstVals_mono hle hformationTypes htypes
  exact ⟨params, resultLevel, envTypes, htypes,
    fun type htype => ⟨(htypeShapes type htype).1, (htypeShapes type htype).2.mono hle⟩,
    fun type htype ctor hctor =>
      let Hctor := hctorShapes type htype ctor hctor
      ⟨Hctor.1.mono hformationTypesLE, Hctor.2.mono hformationTypesLE⟩, hraw⟩

theorem VInductDecl.OrdinaryFormationWF.sourceParameterWF
    {env : VEnv} {decl : VInductDecl}
    (H : VInductDecl.OrdinaryFormationWF env decl) :
    VInductDecl.SourceParameterWF env decl := by
  rcases H with
    ⟨params, _resultLevel, envTypes, htypes, Htypes, Hconstructors, Hraw⟩
  exact ⟨params, envTypes, htypes,
    fun type htype => (Htypes type htype).2,
    fun type htype ctor hctor =>
      (Hconstructors type htype ctor hctor).1, Hraw⟩

theorem VInductDecl.SourceParameterWF.rawCtorShape
    {env : VEnv} {decl : VInductDecl}
    (H : VInductDecl.SourceParameterWF env decl) :
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor := by
  rcases H with ⟨_, _, _, _, _, Hraw⟩
  exact Hraw

/-- Source parameter formation transports to a larger environment in which
the family headers can still be installed. -/
theorem VInductDecl.SourceParameterWF.mono_of_addConstVals
    {env env' envTypes' : VEnv} {decl : VInductDecl}
    (H : VInductDecl.SourceParameterWF env decl) (henv : env ≤ env')
    (htypes' : env'.addConstVals decl.typeConstants = some envTypes') :
    VInductDecl.SourceParameterWF env' decl := by
  rcases H with ⟨params, envTypes, htypes, Htypes, Hctors, Hraw⟩
  have hle : envTypes ≤ envTypes' := VEnv.addConstVals_mono henv htypes htypes'
  exact ⟨params, envTypes', htypes',
    fun type htype => (Htypes type htype).mono henv,
    fun type htype ctor hctor => (Hctors type htype ctor hctor).mono hle, Hraw⟩

theorem VInductDecl.SourceWF.sourceTypes
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∀ type ∈ decl.types, type.toVConstant.WF env := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, hwf, _⟩
  exact hwf

/-- In particular, source constructor types are checked before nested lowering.
No fact about the lowered or auxiliary constructors discharges this obligation. -/
theorem VInductDecl.SourceWF.sourceConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∃ envTypes,
      env.addConstVals decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, _, hwf⟩
  exact ⟨envTypes, htypes, hwf⟩

/-- A compiled block is semantically well formed when every declaration is
well formed at the stage where it is installed, and installation succeeds. -/
def VInductBlock.WF (env : VEnv) (block : VInductBlock) : Prop :=
  ∃ envTypes envCtors envRecursors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    (envCtors.addProjections block.projections).addConstVals
      block.recursors = some envRecursors ∧
    (∀ ci ∈ block.types, ci.toVConstant.WF env) ∧
    (∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes) ∧
    (∀ ci ∈ block.recursors,
      ci.toVConstant.WF (envCtors.addProjections block.projections)) ∧
    ∀ df ∈ block.rules, df.WF envRecursors

theorem VInductBlock.WF.exists_install (H : VInductBlock.WF env block) :
    ∃ env', VInductBlock.install env block = some env' := by
  rcases H with ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, _⟩
  exact ⟨envRecursors.addDefEqRules block.rules, by
    simp [VInductBlock.install, htypes, hctors, hrecs]⟩

/-- Consume an exact forall prefix with the supplied arguments. Ill-shaped
inputs are left unchanged; the formation judgments rule that branch out. -/
def VExpr.instantiateForallPrefix : VExpr → List VExpr → VExpr
  | type, [] => type
  | .forallE _ body, arg :: args =>
    instantiateForallPrefix (body.inst arg) args
  | type, _ :: _ => type

@[simp] theorem VExpr.wrapLams_append
    (left right : List VExpr) (body : VExpr) :
    VExpr.wrapLams (left ++ right) body =
      VExpr.wrapLams left (VExpr.wrapLams right body) := by
  simp [wrapLams, List.foldr_append]

/-- An application spine headed by a constant has no leading binders. -/
theorem VExpr.forallArity_eq_zero_of_getAppFnArgs
    {e : VExpr} {name : Name} {levels : List VLevel} {args : List VExpr}
    (H : e.getAppFnArgs = (.const name levels, args)) : e.forallArity = 0 := by
  cases e with
  | app fn arg => rfl
  | forallE dom body =>
    change VExpr.getAppFnArgs.go (.forallE dom body) [] = _ at H
    simp [VExpr.getAppFnArgs.go] at H
  | _ => rfl

/-- The field count recorded by a raw constructor shape is its syntactic
arity beyond the common parameters. -/
theorem VInductDecl.RawCtorShape.forallArity
    {decl : VInductDecl} {type : VInductiveType} {ctor : VConstVal}
    (H : decl.RawCtorShape type ctor) :
    ∃ doms result,
      ctor.type = VExpr.wrapForalls doms result ∧
      decl.nparams ≤ doms.length ∧
      decl.RawIndAppAt (some type.name) (doms.length - decl.nparams) result ∧
      result.getAppFnArgs.1 = .const type.name (VLevel.params decl.uvars) ∧
      ctor.type.forallArity = doms.length := by
  rcases H with ⟨doms, result, heq, hle, hvalid, hhead⟩
  refine ⟨doms, result, heq, hle, hvalid, hhead, ?_⟩
  have hzero : result.forallArity = 0 := by
    have hspine : result.getAppFnArgs =
        (.const type.name (VLevel.params decl.uvars), result.getAppFnArgs.2) := by
      rw [← hhead]
    exact VExpr.forallArity_eq_zero_of_getAppFnArgs hspine
  rw [heq, VExpr.forallArity_wrapForalls, hzero, Nat.add_zero]

/-- `e` is an application of one of the constructor fields represented by its
de Bruijn index at the outside of the rule telescope. `depth` accounts for
binders introduced inside a higher-order recursive call. -/
def VExpr.IsFieldApp (fieldVars : List Nat) (depth : Nat) (e : VExpr) : Prop :=
  ∃ field ∈ fieldVars, ∃ args,
    e.getAppFnArgs = (.bvar (field + depth), args)

def VExpr.bvarHead? (e : VExpr) : Option Nat :=
  match e.getAppFnArgs.1 with
  | .bvar i => some i
  | _ => none

/-- Syntactic guard for an iota-rule right-hand side. A recursor constant may
only occur through `recCall`, and its major premise must be an application of
a designated constructor field. Ordinary applications cannot smuggle in a
recursor because the `const` constructor excludes their names. -/
inductive VExpr.GuardedIota (recursors : List Name) (fieldVars : List Nat) :
    Nat → VExpr → Prop
  | bvar : GuardedIota recursors fieldVars depth (.bvar n)
  | sort : GuardedIota recursors fieldVars depth (.sort u)
  | const : name ∉ recursors →
      GuardedIota recursors fieldVars depth (.const name levels)
  | app :
      GuardedIota recursors fieldVars depth fn →
      GuardedIota recursors fieldVars depth arg →
      GuardedIota recursors fieldVars depth (.app fn arg)
  | lam :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.lam dom body)
  | forallE :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.forallE dom body)
  | proj :
      GuardedIota recursors fieldVars depth major →
      GuardedIota recursors fieldVars depth (.proj typeName index major)
  | recCall :
      recursor ∈ recursors →
      (∀ arg ∈ init ++ [major],
        GuardedIota recursors fieldVars depth arg) →
      major.IsFieldApp fieldVars depth →
      GuardedIota recursors fieldVars depth
        (VExpr.mkApps (.const recursor levels) (init ++ [major]))

/-- Guardedness for the closed RHS stored in a definitional equation.
Top-level lambdas are the equation telescope, so their bound constructor
fields become the free field variables of the residual iota body.  Testing
the complete closed lambda with an increasing `GuardedIota` depth would
instead (and incorrectly) classify every bound field as non-recursive.

Binder domains are checked with an empty field set, which permits ordinary
types but no recursive call.  Once the telescope is peeled, the residual
body uses the ordinary guarded-iota judgment at depth zero. -/
inductive VExpr.GuardedRuleRhs (recursors : List Name) : VExpr → Prop
  | body (fieldVars : List Nat) :
      GuardedIota recursors fieldVars 0 expression →
      GuardedRuleRhs recursors expression
  | lam :
      GuardedIota recursors [] 0 domain →
      GuardedRuleRhs recursors body →
      GuardedRuleRhs recursors (.lam domain body)

/-- Guardedness depends on the recursor collection only through membership.
This permits an executable checker to use the concrete restoration order and
the abstract block proof to use its generated recursor order, once those two
orders have been identified extensionally. -/
theorem VExpr.GuardedIota.congrRecursors
    {expression : VExpr} {recursors recursors' : List Name}
    {fieldVars : List Nat} {depth : Nat}
    (hsame : ∀ name, name ∈ recursors ↔ name ∈ recursors')
    (H : expression.GuardedIota recursors fieldVars depth) :
    expression.GuardedIota recursors' fieldVars depth := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const fresh =>
      exact .const (fun hmem => fresh ((hsame _).mpr hmem))
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | proj _ ihMajor => exact .proj ihMajor
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody
  | recCall recursorMem arguments majorField ihArguments =>
      exact .recCall ((hsame _).mp recursorMem) ihArguments majorField

theorem VExpr.GuardedRuleRhs.congrRecursors
    {expression : VExpr} {recursors recursors' : List Name}
    (hsame : ∀ name, name ∈ recursors ↔ name ∈ recursors')
    (H : expression.GuardedRuleRhs recursors) :
    expression.GuardedRuleRhs recursors' := by
  induction H with
  | body fieldVars guarded =>
      exact .body fieldVars (guarded.congrRecursors hsame)
  | lam domainGuarded _ ihBody =>
      exact .lam (domainGuarded.congrRecursors hsame) ihBody

def VInductDecl.ownedConstructors
    (decl : VInductDecl) : List (VInductiveType × VConstVal) :=
  decl.types.flatMap fun type => type.ctors.map (type, ·)

def VInductDecl.recursorName (_decl : VInductDecl) (type : VInductiveType) : Name :=
  .mkStr type.name "rec"

/-- A constructor argument selected for an induction hypothesis, together
with the independent recursive-result certificate produced for its domain. -/
structure VInductDecl.RecursiveField (env : VEnv) (decl : VInductDecl) where
  /-- Zero-based position among the constructor fields, after the common
  parameter prefix. -/
  fieldIndex : Nat
  arg : VExpr
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArg env ctx depth domain

def VInductDecl.RecursiveField.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    decl.RecursiveField env' where
  fieldIndex := H.fieldIndex
  arg := H.arg
  ctx := H.ctx
  depth := H.depth
  domain := H.domain
  recursive := H.recursive.mono henv

@[simp] theorem VInductDecl.RecursiveField.mono_fieldIndex
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    (H.mono henv).fieldIndex = H.fieldIndex := rfl

@[simp] theorem VInductDecl.RecursiveField.mono_arg
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    (H.mono henv).arg = H.arg := rfl

/-- Recursor result with an explicit motive count.  Ordinary compilation has
one motive per source family; nested compilation may append motives for
auxiliary families while keeping each source owner's position. -/
def VInductDecl.recursorResultWithCounts (_decl : VInductDecl)
    (ownerIdx numMotives numMinors : Nat) (owner : VInductiveType) : VExpr :=
  let motiveOffset :=
    1 + owner.numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indexVars := (List.range owner.numIndices).reverse.map fun i =>
    VExpr.bvar (i + 1)
  VExpr.mkApps (.bvar motiveOffset) (indexVars ++ [.bvar 0])

def VInductDecl.recursorResult (decl : VInductDecl)
    (ownerIdx numMinors : Nat) (owner : VInductiveType) : VExpr :=
  decl.recursorResultWithCounts ownerIdx decl.types.length numMinors owner

/-- Independent shape of a generated recursor. Besides its conventional name
and universe count, the leading telescope contains exactly the common
parameters, one motive per mutual type, one minor per constructor, the owner's
indices, and one major premise; its result applies the matching motive to the
indices and major premise. -/
structure VInductDecl.RecursorShape (decl : VInductDecl)
    (owner : VInductiveType) (recursor : VConstVal) where
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  owner_eq : decl.types[ownerIdx] = owner
  name : recursor.name = decl.recursorName owner
  uvars : recursor.uvars = decl.uvars ∨ recursor.uvars = decl.uvars + 1
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  afterParams : VExpr
  afterMotives : VExpr
  afterMinors : VExpr
  afterIndices : VExpr
  result : VExpr
  params_take : recursor.type.takeForalls decl.nparams =
    some (params, afterParams)
  motives_take : afterParams.takeForalls decl.types.length =
    some (motives, afterMotives)
  minors_take : afterMotives.takeForalls decl.ownedConstructors.length =
    some (minors, afterMinors)
  indices_take : afterMinors.takeForalls owner.numIndices =
    some (indices, afterIndices)
  major_take : afterIndices.takeForalls 1 = some (major, result)
  result_eq : result = decl.recursorResult ownerIdx minors.length owner

/-- Build a `RecursorShape` from the single wrapped
telescope produced by recursor generation. -/
def VInductDecl.RecursorShape.ofWrapped
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    {ownerIdx : Nat} {params motives minors indices major : List VExpr}
    {result : VExpr}
    (owner_lt : ownerIdx < decl.types.length)
    (owner_eq : decl.types[ownerIdx] = owner)
    (name : recursor.name = decl.recursorName owner)
    (uvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (hparams : params.length = decl.nparams)
    (hmotives : motives.length = decl.types.length)
    (hminors : minors.length = decl.ownedConstructors.length)
    (hindices : indices.length = owner.numIndices)
    (hmajor : major.length = 1)
    (htype : recursor.type = VExpr.wrapForalls
      (params ++ motives ++ minors ++ indices ++ major) result)
    (hresult : result = decl.recursorResult ownerIdx minors.length owner) :
    decl.RecursorShape owner recursor := by
  refine {
    ownerIdx, owner_lt, owner_eq, name, uvars, params, motives, minors, indices,
    major
    afterParams := VExpr.wrapForalls (motives ++ minors ++ indices ++ major) result
    afterMotives := VExpr.wrapForalls (minors ++ indices ++ major) result
    afterMinors := VExpr.wrapForalls (indices ++ major) result
    afterIndices := VExpr.wrapForalls major result
    result
    params_take := ?_
    motives_take := ?_
    minors_take := ?_
    indices_take := ?_
    major_take := ?_
    result_eq := hresult }
  · rw [← hparams]
    rw [htype]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append params
        (motives ++ minors ++ indices ++ major) result
  · rw [← hmotives]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append motives
        (minors ++ indices ++ major) result
  · rw [← hminors]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append minors (indices ++ major) result
  · rw [← hindices]
    exact VExpr.takeForalls_wrapForalls_append indices major result
  · rw [← hmajor]
    exact VExpr.takeForalls_wrapForalls major result

/-- Shape of a restored source recursor of a nested declaration.  Lowering
appends auxiliary families and constructors to the mutual block, so their
motives and minors remain in the restored source recursor's telescope.  The
source families and constructors form prefixes of those two groups; the
source owner keeps its motive position. -/
structure VInductDecl.NestedRecursorShape (decl : VInductDecl)
    (owner : VInductiveType) (recursor : VConstVal) where
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  owner_eq : decl.types[ownerIdx] = owner
  name : recursor.name = decl.recursorName owner
  uvars : recursor.uvars = decl.uvars ∨ recursor.uvars = decl.uvars + 1
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  source_motives : decl.types.length ≤ motives.length
  source_minors : decl.ownedConstructors.length ≤ minors.length
  afterParams : VExpr
  afterMotives : VExpr
  afterMinors : VExpr
  afterIndices : VExpr
  result : VExpr
  params_take : recursor.type.takeForalls decl.nparams =
    some (params, afterParams)
  motives_take : afterParams.takeForalls motives.length =
    some (motives, afterMotives)
  minors_take : afterMotives.takeForalls minors.length =
    some (minors, afterMinors)
  indices_take : afterMinors.takeForalls owner.numIndices =
    some (indices, afterIndices)
  major_take : afterIndices.takeForalls 1 = some (major, result)
  result_eq : result = decl.recursorResultWithCounts ownerIdx
    motives.length minors.length owner

/-- Build a `NestedRecursorShape` from its complete
restored telescope. -/
def VInductDecl.NestedRecursorShape.ofWrapped
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    {ownerIdx : Nat} {params motives minors indices major : List VExpr}
    {result : VExpr}
    (owner_lt : ownerIdx < decl.types.length)
    (owner_eq : decl.types[ownerIdx] = owner)
    (name : recursor.name = decl.recursorName owner)
    (uvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (hparams : params.length = decl.nparams)
    (hsourceMotives : decl.types.length ≤ motives.length)
    (hsourceMinors : decl.ownedConstructors.length ≤ minors.length)
    (hindices : indices.length = owner.numIndices)
    (hmajor : major.length = 1)
    (htype : recursor.type = VExpr.wrapForalls
      (params ++ motives ++ minors ++ indices ++ major) result)
    (hresult : result = decl.recursorResultWithCounts ownerIdx
      motives.length minors.length owner) :
    decl.NestedRecursorShape owner recursor := by
  refine {
    ownerIdx, owner_lt, owner_eq, name, uvars, params, motives, minors, indices,
    major, source_motives := hsourceMotives, source_minors := hsourceMinors
    afterParams := VExpr.wrapForalls (motives ++ minors ++ indices ++ major) result
    afterMotives := VExpr.wrapForalls (minors ++ indices ++ major) result
    afterMinors := VExpr.wrapForalls (indices ++ major) result
    afterIndices := VExpr.wrapForalls major result
    result
    params_take := ?_
    motives_take := ?_
    minors_take := ?_
    indices_take := ?_
    major_take := ?_
    result_eq := hresult }
  · rw [← hparams, htype]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append params
        (motives ++ minors ++ indices ++ major) result
  · simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append motives
        (minors ++ indices ++ major) result
  · simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append minors
        (indices ++ major) result
  · rw [← hindices]
    exact VExpr.takeForalls_wrapForalls_append indices major result
  · rw [← hmajor]
    exact VExpr.takeForalls_wrapForalls major result

/-- Ordinary recursors are the zero-auxiliary special case of nested
recursors. -/
def VInductDecl.RecursorShape.toNested
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    (H : decl.RecursorShape owner recursor) :
    decl.NestedRecursorShape owner recursor where
  ownerIdx := H.ownerIdx
  owner_lt := H.owner_lt
  owner_eq := H.owner_eq
  name := H.name
  uvars := H.uvars
  params := H.params
  motives := H.motives
  minors := H.minors
  indices := H.indices
  major := H.major
  source_motives := Nat.le_of_eq
    (VExpr.takeForalls_domains_length H.motives_take).symm
  source_minors := Nat.le_of_eq
    (VExpr.takeForalls_domains_length H.minors_take).symm
  afterParams := H.afterParams
  afterMotives := H.afterMotives
  afterMinors := H.afterMinors
  afterIndices := H.afterIndices
  result := H.result
  params_take := H.params_take
  motives_take := by
    rw [VExpr.takeForalls_domains_length H.motives_take]
    exact H.motives_take
  minors_take := by
    rw [VExpr.takeForalls_domains_length H.minors_take]
    exact H.minors_take
  indices_take := H.indices_take
  major_take := H.major_take
  result_eq := by
    rw [VExpr.takeForalls_domains_length H.motives_take]
    simpa [VInductDecl.recursorResult] using H.result_eq

/-- Reinterpret an expanded nested-recursor telescope at a compatible source
declaration.  Auxiliary motives
and minors remain in the telescope, while the source declaration supplies
the source family prefix, universe/parameter metadata, and owner. -/
def VInductDecl.NestedRecursorShape.ofCompatible
    {loweredDecl sourceDecl : VInductDecl}
    {loweredOwner sourceOwner : VInductiveType} {recursor : VConstVal}
    (H : loweredDecl.NestedRecursorShape loweredOwner recursor)
    (howner : H.ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[H.ownerIdx] = sourceOwner)
    (hname : recursor.name = sourceDecl.recursorName sourceOwner)
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (hnparams : sourceDecl.nparams = loweredDecl.nparams)
    (hmotives : sourceDecl.types.length ≤ H.motives.length)
    (hminors : sourceDecl.ownedConstructors.length ≤ H.minors.length)
    (hindices : sourceOwner.numIndices = loweredOwner.numIndices) :
    sourceDecl.NestedRecursorShape sourceOwner recursor where
  ownerIdx := H.ownerIdx
  owner_lt := howner
  owner_eq := hownerEq
  name := hname
  uvars := huvars
  params := H.params
  motives := H.motives
  minors := H.minors
  indices := H.indices
  major := H.major
  source_motives := hmotives
  source_minors := hminors
  afterParams := H.afterParams
  afterMotives := H.afterMotives
  afterMinors := H.afterMinors
  afterIndices := H.afterIndices
  result := H.result
  params_take := by simpa [hnparams] using H.params_take
  motives_take := H.motives_take
  minors_take := H.minors_take
  indices_take := by simpa [hindices] using H.indices_take
  major_take := H.major_take
  result_eq := by
    rw [H.result_eq]
    simp only [VInductDecl.recursorResultWithCounts]
    rw [hindices]

/-- One declarative iota equation. The left-hand side is a recursor whose final
argument is the matching constructor application. The right-hand side may call
any sibling recursor in a mutual block, but only on explicitly identified
constructor fields. Typing of the complete equation is supplied separately by
`VInductBlock.WF`. -/
structure VInductDecl.IotaRule (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)
  recursiveFields : List (decl.RecursiveField env)
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = recursiveFields.map (·.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ recursiveFields,
    ∃ h : field.fieldIndex < (ctorArgs.drop decl.nparams).length,
      field.arg = (ctorArgs.drop decl.nparams)[field.fieldIndex]'h
  recursiveArgs : List VExpr
  recursiveArgs_eq : recursiveArgs = recursiveFields.map (·.arg)
  recursive_args : List.Sublist recursiveArgs (ctorArgs.drop decl.nparams)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  rhsArgs : List VExpr
  rhs_spine : rhsBody.getAppFnArgs = (.bvar minorVar, rhsArgs)
  field_args : rhsArgs.take (ctorArgs.length - decl.nparams) =
    ctorArgs.drop decl.nparams
  recursive_results :
    (rhsArgs.drop (ctorArgs.length - decl.nparams)).length = recursiveArgs.length
  rhs_guarded : rhsBody.GuardedIota (block.recursors.map (·.name)) fieldVars 0

/-- A constructor field selected by a restored nested equation.  Unlike
`RecursiveField`, this record does not claim that the source field has a
direct mutual-family head: a genuinely nested field may instead be handled
by one of the restored auxiliary recursors. -/
structure VInductDecl.NestedIotaField where
  fieldIndex : Nat
  arg : VExpr

/-- Declarative iota equation for a restored source recursor of a nested declaration.

The motives and minors of the auxiliary families remain in the restored source
recursor's telescope, so their exact counts come from the same
`NestedRecursorShape` as the recursor itself.  Recursive arguments are
recorded by their ordered constructor-field positions rather than by
`RecursiveArg`: the latter deliberately recognizes only direct mutual-family
heads and therefore cannot classify fields such as `List Tree`.

Typing of the equation remains an independent obligation of
`VInductBlock.WF`; together with `rhs_guarded`, it ensures that every selected
field is used only by a well-typed restored recursor call. -/
structure VInductDecl.NestedIotaRule
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_shape : decl.NestedRecursorShape owner recursor
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams +
    recursor_shape.motives.length + recursor_shape.minors.length +
      owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams +
    recursor_shape.motives.length + recursor_shape.minors.length +
      (ctorArgs.length - decl.nparams)
  recursiveFields : List NestedIotaField
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = recursiveFields.map (·.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ recursiveFields,
    ∃ h : field.fieldIndex < (ctorArgs.drop decl.nparams).length,
      field.arg = (ctorArgs.drop decl.nparams)[field.fieldIndex]'h
  recursiveArgs : List VExpr
  recursiveArgs_eq : recursiveArgs = recursiveFields.map (·.arg)
  recursive_args : List.Sublist recursiveArgs (ctorArgs.drop decl.nparams)
  fieldVars : List Nat
  fieldVars_eq : fieldVars = recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  rhsArgs : List VExpr
  rhs_spine : rhsBody.getAppFnArgs = (.bvar minorVar, rhsArgs)
  field_args : rhsArgs.take (ctorArgs.length - decl.nparams) =
    ctorArgs.drop decl.nparams
  recursive_results :
    (rhsArgs.drop (ctorArgs.length - decl.nparams)).length =
      recursiveArgs.length
  rhs_guarded : rhsBody.GuardedIota
    (block.recursors.map (·.name)) fieldVars 0

end Lean4Lean
