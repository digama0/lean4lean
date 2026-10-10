import Lean4Lean.Verify.Inductive.Constructor.Tails
import Lean4Lean.Verify.Inductive.Header.Block
import Lean4Lean.Verify.ExprParamUniform

/-! Refinement of the executable constructor check (`checkConstructors.loopCtor`)
and positivity check (`checkPositivity`): the parameter and field branches,
the recursive-application test (`isValidIndAppIdx`) and the declarative
positivity rules, run in the checking scope of the constructor check. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkConstructors.loopCtors

theorem result.WF
    (hidx : ¬ ctorIdx < ctors.length) (hQ : Q []) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx]
  exact Except.WF.pure hQ

/-- One constructor-loop iteration up to the already verified telescope
checker. The continuation receives the closed source translation before
choosing the public `CtorShape` refinement. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun fields =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF fun rest =>
          Q (fields :: rest)) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  rw [if_neg (by simpa using hfresh)]
  exact (checkClosedType.WF Hc).bind fun _ hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
      ((AddInductive.checkConstructors.loopCtor stats isUnsafe
          ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
          c'.fuel.inductiveFuel >>= fun fields => do
        return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
          (foundCtors.insert ctors[ctorIdx].name))) : AddInductive.M (List (List Bool))) c).WF Q
    have hread : ((read : AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine hread.bind fun c' hc' => ?_
    subst c'
    exact (Hloop _ type' checkedType' hchecked).bind fun fields hnext =>
      hnext.bind fun rest hrest => Except.WF.pure hrest

/-- One constructor-loop iteration, including the executable's duplicate-name
guard.  A duplicate takes the executable error branch; only the successful
branch reaches the semantic constructor checker. -/
theorem stepPrefix.checkedWF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun fields =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF fun rest =>
          Q (fields :: rest)) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  cases hfresh : foundCtors.contains ctors[ctorIdx].name with
  | false => exact stepPrefix.WF Hc hidx hfresh Hloop
  | true =>
      rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
      simp only [hfresh, ↓reduceIte]
      exact Except.WF.throw

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

theorem result.WF
    (hidx : ¬ targetIdx < indTypes.size) (hQ : Q []) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx]
  exact Except.WF.pure hQ

theorem step.WF
    (hidx : targetIdx < indTypes.size)
    (Hctors :
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        indTypes[targetIdx].ctors 0 {} c).WF fun fields =>
      (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
        (targetIdx + 1) c).WF fun rest => Q (fields :: rest)) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx]
  exact Hctors.bind fun _ hnext => hnext.bind fun _ hrest => Except.WF.pure hrest

end checkConstructors.loopTypes

namespace checkConstructors.loopCtor

theorem zero.WF :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkConstructors.loopCtor] at h

/-- A constructor telescope ending in the checked target application returns
success.  This theorem does not relate `isValidIndAppIdx` to
`VInductDecl.ValidIndAppAt`. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hQ : Q []) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals exact Except.WF.pure hQ

/-- An invalid non-forall constructor target is rejected. -/
theorem invalidResult.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = false) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Common-parameter branch of a constructor telescope.  The cached parameter
type comparison is converted directly into abstract body instantiation. -/
theorem parameter.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = some param)
    (hget : (AddInductive.getType param c).WF
      (fun ty => ty = paramTy ∧ ty = paramTyN))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx param param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (j : Nat) (hj : j ≤ Hc.mlctx.length)
    (hfv : paramCheckFVars stats i = (Hc.mlctx.dropN j hj).fvarList)
    (hdom₀ : TrExprS Hc.venv c.lparams (Hc.mlctx.dropN j hj).vlctx dom dom₀)
    (hparamTy₀ : TrExprS Hc.venv c.lparams (Hc.mlctx.dropN j hj).vlctx
      paramTyN paramTy₀)
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      Hc.venv.IsDefEqU c.lparams.length (Hc.mlctx.dropN j hj).vlctx.toCtx
        dom₀ paramTy₀ →
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 param) (body'.inst param') →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel c).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  change (AddInductive.getType param c >>= fun paramTy =>
    ((do
      unless ← AddInductive.withCheckLCtx (← AddInductive.paramCheckLCtx stats i)
          (TypeChecker.isDefEq dom paramTy) do
        throw <| .other
          s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel) : AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' ⟨hparamTyEq, hparamTyEqN⟩ => ?_
  subst paramTy'
  subst hparamTyEqN
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  let Hci := Hc.paramCheck stats i j hj hfv
  refine (isDefEqInContext.checkingWF Hci hdom₀ hparamTy₀).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq₀ := hequal rfl
    have heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx dom' paramTy' :=
      Hci.check.embed.isDefEqU Hc.checking.tr.wf hdom₀ hparamTy₀ hdom hparamTy heq₀
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact Hrec heq heq₀ hopened

/-- Safe constructor-field branch.  Successful field typing, the executable
universe bound, positivity, annotation transport, and fresh body opening are
all delivered to the recursive continuation. -/
theorem safeField.sourceWF
    {Pos : Bool → Prop}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF Pos)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      ∀ fieldType₀, TrExprS Hc.venv c.lparams Hc.chk.vlctx dom fieldType₀ →
      Hc.venv.HasType c.lparams.length Hc.chk.vlctx.toCtx
        fieldType₀ (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ recursive, Pos recursive →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ body₀'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom₀ :: Hc.chk.vlctx.toCtx) sourceBody₀ body₀'' →
        TrExprS Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        TrExprS Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body₀'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF
          fun rest => Q (recursive :: rest)) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.dualWF Hc Hdom.source Hdom₀.source).bind
    fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldLevel, fieldLevel', rfl, hfieldLevel, hfieldHasType,
    fieldType₀, hfieldType₀, hfieldHasType₀⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    let recursive ← if !false then AddInductive.checkPositivity stats dom ctor i
      else pure false
    AddInductive.withUnannotatedCheckedLocalDecl name bi dom fun arg => do
      return recursive :: (← AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel)) : AddInductive.M (List Bool)) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    refine Hpos.bind fun recursive hpos => ?_
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    rcases Hdom₀.body Hc.atCheckLCtx hbody₀ with ⟨body₀'', hbody₀'', hbodyEq₀⟩
    refine withCheckedLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg => do
        return recursive :: (← AddInductive.checkConstructors.loopCtor stats false ctor
          targetIdx (body.instantiate1 arg) (i + 1) fuel))
      Hc Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.unannotated Hdom.isType hbody''
    have hopened₀ := Hc.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
      Hdom₀.unannotated Hdom₀.isType hbody₀''
    exact (Hrec _ fieldLevel fieldLevel' Hdom.source hfieldLevel
      hfieldHasType fieldType₀ hfieldType₀ hfieldHasType₀ hbound recursive hpos body''
      hbodyEq body₀'' hbodyEq₀ hopened hopened₀).bind fun _ hrest =>
        Except.WF.pure hrest
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Unsafe constructor-field branch: the same source typing, universe, and
annotation obligations apply, while positivity is intentionally skipped. -/
theorem unsafeField.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      ∀ fieldType₀, TrExprS Hc.venv c.lparams Hc.chk.vlctx dom fieldType₀ →
      Hc.venv.HasType c.lparams.length Hc.chk.vlctx.toCtx
        fieldType₀ (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ body₀'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom₀ :: Hc.chk.vlctx.toCtx) sourceBody₀ body₀'' →
        TrExprS Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        TrExprS Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body₀'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF
          fun rest => Q (false :: rest)) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.dualWF Hc Hdom.source Hdom₀.source).bind
    fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldLevel, fieldLevel', rfl, hfieldLevel, hfieldHasType,
    fieldType₀, hfieldType₀, hfieldHasType₀⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    let recursive ← if !true then AddInductive.checkPositivity stats dom ctor i
      else pure false
    AddInductive.withUnannotatedCheckedLocalDecl name bi dom fun arg => do
      return recursive :: (← AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel)) : AddInductive.M (List Bool)) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    rcases Hdom₀.body Hc.atCheckLCtx hbody₀ with ⟨body₀'', hbody₀'', hbodyEq₀⟩
    refine withCheckedLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg => do
        return false :: (← AddInductive.checkConstructors.loopCtor stats true ctor
          targetIdx (body.instantiate1 arg) (i + 1) fuel))
      Hc Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.unannotated Hdom.isType hbody''
    have hopened₀ := Hc.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
      Hdom₀.unannotated Hdom₀.isType hbody₀''
    exact (Hrec _ fieldLevel fieldLevel' Hdom.source hfieldLevel
      hfieldHasType fieldType₀ hfieldType₀ hfieldHasType₀ hbound body'' hbodyEq
      body₀'' hbodyEq₀ hopened hopened₀).bind fun _ hrest => Except.WF.pure hrest
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkConstructors.loopCtor

namespace checkPositivityStep

theorem hasIndOcc_eq_findAny :
    AddInductive.hasIndOcc indConsts type =
      type.findAny (fun
        | .const name _ => indConsts.any fun I => I.constName! == name
        | _ => false) := by
  rfl

def IndConstNames (indConsts : Array Expr) (names : List Name) : Prop :=
  ∀ name, (indConsts.any fun I => I.constName! == name) = names.contains name

/-- The concrete array accumulated by header checking has exactly the abstract
mutual-family names, in declaration order.  Keeping this stronger structural
fact separate makes the weaker search correspondence above reusable by both
positivity and recursive-target validation. -/
structure IndConstArray (levels : List Level) (indConsts : Array Expr)
    (names : List Name) : Prop where
  exact : indConsts = (names.map fun name => .const name levels).toArray
  names : IndConstNames indConsts names

/-- The portion of the mutable header statistics needed to interpret a
recursive application in the independent declaration.  In particular, the
common parameters are related by expression translation rather than merely by
array position. -/
structure ValidAppStatsWF (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

theorem List.mapM_some_length
    {xs : List α} {ys : List β} {f : α → Option β}
    (H : xs.mapM f = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp at H
    subst ys
    rfl
  | cons x xs ih =>
    cases hx : f x <;> simp [hx] at H
    rename_i y
    cases hxs : xs.mapM f <;> simp [hxs] at H
    rename_i ys'
    subst ys
    simp [ih hxs]

theorem forall₂_get?_eq_some
    {R : α → β → Prop} {as : List α} {bs : List β}
    {i : Nat} {a : α} {b : β}
    (H : List.Forall₂ R as bs)
    (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at ha hb
      subst a
      subst b
      exact h
    | succ i => exact ih (by simpa using ha) (by simpa using hb)

theorem ValidAppStatsWF.params_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.params.size = decl.nparams := by
  have := List.Forall₂.length_eq H.params
  simpa [VInductDecl.paramVars] using this

theorem ValidAppStatsWF.types_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem ValidAppStatsWF.indConstAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem ValidAppStatsWF.nindicesAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem ValidAppStatsWF.paramAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env Us Δ stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlen := List.Forall₂.length_eq H.params
      simpa using hlen ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    forall₂_get?_eq_some H.params hsource htarget⟩

theorem ValidAppStatsWF.paramFVarAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

theorem forall₂_map_right
    (H : List.Forall₂ R as bs)
    (hf : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S as (bs.map f) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

@[simp] theorem VInductDecl.paramVars_liftN
    {decl : VInductDecl} {depth : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN 1 e 0) =
      decl.paramVars (depth + 1) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  omega

@[simp] theorem VInductDecl.paramVars_liftN_many
    {decl : VInductDecl} {depth n : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN n e 0) =
      decl.paramVars (depth + n) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  congr 2
  omega


/-- Extend application statistics in an independently tracked semantic scope.
Unlike `withLocalDecl`, this theorem does not require the executable context
to be that scope; the already verified target-context extension is sufficient
for weakening the cached parameter translations. -/
theorem ValidAppStatsWF.withFVar
    (H : ValidAppStatsWF env Us scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    ValidAppStatsWF env Us
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS env Us
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.orderedStrong W hscope'
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

theorem IndConstArray.empty (levels : List Level) :
    IndConstArray levels #[] [] where
  exact := rfl
  names := by simp [IndConstNames, Array.any]

theorem IndConstArray.ofExact
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (h : indConsts = (names.map fun name => .const name levels).toArray) :
    IndConstArray levels indConsts names where
  exact := h
  names := by
    intro name
    apply Bool.eq_iff_iff.mpr
    simp [h]
    constructor
    · rintro ⟨source, hsource, hname⟩
      have : source = name := by
        simpa [Expr.constName!] using hname
      simpa [this] using hsource
    · intro hname
      exact ⟨name, hname, by simp [Expr.constName!]⟩

/-- Promote the exact traversal-facing statistics into the positivity-facing
application invariant. -/
theorem ValidAppStatsWF.ofHeaderStats
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us Δ stats decl depth where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.params
  paramFVars := H.paramFVars

theorem ValidAppStatsWF.ofHeaderStatsScoped
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us H.parameterScope stats decl 0 where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.suffixParams
  paramFVars := H.paramFVars

def LiteralDisjoint (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal,
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

/-- The literal-expansion condition needed by translation is only required
for literals supported by the current environment.  This is strictly weaker
than `LiteralDisjoint` while the prelude is declared, when (for example) the freshly
declared `Char` family exists but string literals are not available yet. -/
def AvailableLiteralDisjoint (env : VEnv) (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal, env.ContainsLits literal →
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

theorem LiteralDisjoint.available
    (H : LiteralDisjoint indConsts) :
    AvailableLiteralDisjoint env indConsts :=
  fun literal _ => H literal

/-- Literal availability depends only on the constant map, which projection
registration leaves unchanged. -/
theorem AvailableLiteralDisjoint.addProjections
    (H : AvailableLiteralDisjoint env indConsts)
    (entries : List VProjectionEntry) :
    AvailableLiteralDisjoint (env.addProjections entries) indConsts := by
  intro literal hlit
  apply H literal
  cases literal with
  | natVal _ => simpa [VEnv.ContainsLits, VEnv.contains] using hlit
  | strVal _ => simpa [VEnv.ContainsLits, VEnv.contains] using hlit

/-- Split the right-hand list at the boundary forced by an appended
left-hand list in a `Forall₂` derivation. -/
alias forall₂_append := _root_.List.Forall₂.append'

theorem List.Forall₂.split_left
    (H : List.Forall₂ R (as ++ bs) cs) :
    ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧
      List.Forall₂ R as cs₁ ∧ List.Forall₂ R bs cs₂ := by
  induction as generalizing cs with
  | nil => exact ⟨[], cs, by simp, .nil, H⟩
  | cons a as ih =>
      cases H with
      | cons hab htail =>
        rcases ih htail with ⟨cs₁, cs₂, rfl, hleft, hright⟩
        exact ⟨_ :: cs₁, cs₂, by simp, .cons hab hleft, hright⟩

/-- Exact inversion of a translated concrete application list.  Unlike the
typechecker-oriented `AppStack`, this retains the final abstract spine, which
is needed to split the field arguments and recursive results of an iota RHS. -/
theorem TrExprS.mkAppList_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn args) out) :
    ∃ fn' args',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) args args' ∧
      out = VExpr.mkApps fn' args' := by
  induction args generalizing fn out with
  | nil =>
      exact ⟨out, [], H, .nil, rfl⟩
  | cons arg args ih =>
      simp only [Expr.mkAppList] at H
      rcases ih H with ⟨app', args', happ, hargs, hout⟩
      cases happ with
      | app _ _ hfn harg =>
        refine ⟨_, _ :: args', hfn, .cons harg hargs, ?_⟩
        simpa [VExpr.mkApps] using hout

/-- Pointwise expression translation can be assembled into an application
spine once the independently derived abstract spine is known to be
well-typed.  Inverting that typing derivation supplies the function and
argument premises required by each `TrExprS.app` constructor. -/
theorem TrExprS.mkAppList
    (henv : VEnv.OrderedStrong env)
    (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (hfn : TrExprS env Us Δ fn fn')
    (hargs : List.Forall₂ (TrExprS env Us Δ) args args')
    (happs : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps fn' args')) :
    TrExprS env Us Δ (Expr.mkAppList fn args)
      (VExpr.mkApps fn' args') := by
  induction hargs generalizing fn fn' with
  | nil => simpa [Expr.mkAppList, VExpr.mkApps] using hfn
  | @cons arg arg' args args' harg hargs ih =>
    have hprefix := VExpr.WF.mkApps_fn henv hctx
      (fn := .app fn' arg') (args := args') happs
    rcases hprefix.app_inv henv hctx with
      ⟨domain, body, hfnType, hargType⟩
    have happ : TrExprS env Us Δ (.app fn arg) (.app fn' arg') :=
      .app hfnType hargType hfn harg
    simpa [Expr.mkAppList, VExpr.mkApps] using
      ih (fn := .app fn arg) (fn' := .app fn' arg') happ happs

/-- Application-spine inversion with an exact split between two concrete
argument groups. -/
theorem TrExprS.mkAppList_append_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn (left ++ right)) out) :
    ∃ fn' left' right',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) left left' ∧
      List.Forall₂ (TrExprS env Us Δ) right right' ∧
      out = VExpr.mkApps fn' (left' ++ right') := by
  rcases TrExprS.mkAppList_inv H with
    ⟨fn', args', hfn, hargs, hout⟩
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.List.Forall₂.split_left
    hargs with
    ⟨left', right', rfl, hleft, hright⟩
  exact ⟨fn', left', right', hfn, hleft, hright, hout⟩

/-- Translation preserves a constant-headed application spine and the
left-to-right correspondence of all its arguments.  This is the syntactic fact
needed by both executable recursive-target checks. -/
theorem TrExprS.constAppSpine
    (H : TrExprS env Us Δ e e')
    (hhead : e.getAppFn = .const name levels) :
    ∃ levels' args',
      e'.getAppFnArgs = (.const name levels', args') ∧
      levels.mapM (VLevel.ofLevel Us) = some levels' ∧
      List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  induction e generalizing e' with
  | const _ _ =>
    cases H with
    | const _ hlevels _ =>
      cases hhead
      exact ⟨_, [], rfl, hlevels, .nil⟩
  | app fn arg ihFn _ =>
    cases H
    rename_i f' _ _ arg' _ _ hfn harg
    rcases ihFn hfn hhead with ⟨levels', args', hspine, hlevels, hargs⟩
    have hargs' := List.Forall₂.append' hargs (.cons harg .nil)
    refine ⟨levels', args' ++ [arg'], ?_, hlevels, ?_⟩
    · simp [hspine]
    · simpa only [Expr.getAppArgsList_app] using hargs'
  | bvar _ | fvar _ | sort _ | lit _ => cases hhead
  | mvar _ => cases H
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ _ => cases hhead

theorem TrExprS.eqv_fvar_target
    (H₁ : TrExprS env Us Δ (.fvar fv) e₁')
    (H₂ : TrExprS env Us Δ e₂ e₂')
    (heq : ((.fvar fv : Expr) == e₂) = true) : e₁' = e₂' := by
  cases e₂ <;> simp [(· == ·), Expr.eqv'] at heq
  have hfv : fv = _ := beq_iff_eq.mp heq
  subst_vars
  cases H₁ with
  | fvar h₁ =>
    cases H₂ with
    | fvar h₂ =>
      rw [h₁] at h₂
      cases h₂
      rfl

theorem isValidIndAppIdx.head
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    (type.getAppFn == stats.indConsts[i]!) = true := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.constHead
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels)) :
    type.getAppFn = .const name levels := by
  have hhead := isValidIndAppIdx.head hvalid
  have hget : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  rw [hget] at hhead
  exact Expr.eqv_const.mp hhead

theorem isValidIndAppIdx.arity
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    type.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.param
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hj : j < stats.params.size) :
    (stats.params[j] == type.getAppArgs[j]'(by
      have := isValidIndAppIdx.arity hvalid
      omega)) = true := by
  have hp :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    cases hparams :
        (stats.params == type.getAppArgs.extract 0 stats.params.size) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  rw [Array.beq_eq_decide] at hp
  split at hp
  · rename_i hsize
    simp only [decide_eq_true_eq] at hp
    have helem := hp j hj
    simpa only [Array.getElem_extract, Nat.zero_add] using helem
  · simp_all

theorem isValidIndAppIdx.indexNoOccurrence
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hlower : stats.params.size ≤ j) (hupper : j < type.getAppArgs.size) :
    AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
  have hall :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    have harity := isValidIndAppIdx.arity hvalid
    rw [harity]
    cases hclean :
        (type.getAppArgs.extract stats.params.size
          (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  have hk : j - stats.params.size <
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).size := by
    simp only [Array.size_extract]
    omega
  have hclean := Array.all_eq_true.mp hall (j - stats.params.size) hk
  simp only [Array.getElem_extract] at hclean
  have hj : stats.params.size + (j - stats.params.size) = j := by omega
  simp only [hj] at hclean
  cases hocc : AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] <;>
    simp_all

/-- The observable components of a valid inductive application are also
sufficient for the executable classifier.  This converse keeps later
alpha-renaming arguments independent of the implementation's nested
`unless` encoding. -/
theorem isValidIndAppIdx.intro
    (hhead : (type.getAppFn == stats.indConsts[i]!) = true)
    (harity : type.getAppArgs.size =
      stats.params.size + stats.nindices[i]!)
    (hparam : ∀ j (hj : j < stats.params.size),
      stats.params[j] = type.getAppArgs[j]'(by omega))
    (hindex : ∀ j (hlower : stats.params.size ≤ j)
      (hupper : j < type.getAppArgs.size),
      AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false) :
    AddInductive.isValidIndAppIdx stats type i = true := by
  have hparamsEq :
      stats.params = type.getAppArgs.extract 0 stats.params.size := by
    apply Array.ext
    · simp [harity]
    · intro j hjLeft hjRight
      simpa only [Array.getElem_extract, Nat.zero_add] using hparam j hjLeft
  have hparamsBeq :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    calc
      (stats.params == type.getAppArgs.extract 0 stats.params.size) =
          (stats.params == stats.params) :=
        congrArg (fun xs => stats.params == xs) hparamsEq.symm
      _ = true := beq_self_eq_true stats.params
  have hindices :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    apply Array.all_eq_true.mpr
    intro j hj
    simp only [Array.size_extract] at hj
    simp only [Array.getElem_extract]
    have hclean := hindex (stats.params.size + j) (by omega) (by omega)
    simp [hclean]
  have hindices' :
      (type.getAppArgs.extract stats.params.size
        (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    rw [← harity]
    exact hindices
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq, hhead, harity,
    beq_self_eq_true, Bool.true_and, hparamsBeq, hindices',
    ↓reduceIte]
  rfl

theorem isValidIndAppFrom?_some
    (h : AddInductive.isValidIndAppFrom? stats type start fuel = some i) :
    start ≤ i ∧ i < start + fuel ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  induction fuel generalizing start with
  | zero => simp [AddInductive.isValidIndAppFrom?] at h
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?] at h
    by_cases hvalid : AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hvalid] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hvalid⟩
    · have hfalse : AddInductive.isValidIndAppIdx stats type start = false := by
        cases hv : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hvalid hv)
      simp [hfalse] at h
      rcases ih h with ⟨hlower, hupper, hvalid⟩
      exact ⟨by omega, by omega, hvalid⟩

/-- If any member in the scanned interval validates, the first-match scan
returns some member (possibly an earlier equivalent entry). -/
theorem isValidIndAppFrom?_exists_of_valid
    (hvalid : AddInductive.isValidIndAppIdx stats type target = true)
    (hlower : start ≤ target) (hupper : target < start + fuel) :
    ∃ owner,
      AddInductive.isValidIndAppFrom? stats type start fuel = some owner := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?]
    by_cases hstart :
        AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hstart]
      exact ⟨start, rfl⟩
    · have hstartFalse :
          AddInductive.isValidIndAppIdx stats type start = false := by
        cases h : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hstart h)
      rw [if_neg hstart]
      have hne : start ≠ target := by
        intro heq
        subst target
        exact Bool.noConfusion (hstartFalse.symm.trans hvalid)
      exact ih (start := start + 1) (by omega) (by omega)

theorem isValidIndApp?_exists_of_valid
    (hvalid : AddInductive.isValidIndAppIdx stats type target = true)
    (hconst : stats.indConsts[target]? = some value) :
    ∃ owner, AddInductive.isValidIndApp? stats type = some owner := by
  have htarget : target < stats.indConsts.size :=
    (Array.getElem?_eq_some_iff.mp hconst).1
  simpa [AddInductive.isValidIndApp?] using
    (isValidIndAppFrom?_exists_of_valid hvalid (start := 0)
      (fuel := stats.indConsts.size) (by omega) (by omega))

theorem isValidIndApp?_some
    (h : AddInductive.isValidIndApp? stats type = some i) :
    i < stats.indConsts.size ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  exact ⟨by simpa using (isValidIndAppFrom?_some h).2.1,
    (isValidIndAppFrom?_some h).2.2⟩

/-- Once the preceding validation has identified a family member,
`getIIndices` returns that same member. This isolates the partial `get!` in
the executable helper. -/
theorem getIIndices.fst_eq_of_valid
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 = i := by
  simp only [AddInductive.getIIndices, h, Option.get!_eq_getD,
    Option.getD_some]

/-- The suffix returned by `getIIndices` has the declared index arity of the
selected mutual-family member. -/
theorem getIIndices.index_arity
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size = stats.nindices[i]! := by
  rw [AddInductive.getIIndices]
  change (type.getAppArgs.toSubarray stats.params.size).toArray.size = _
  rw [Subarray.size_toArray, Subarray.size_eq]
  simp only [Array.stop_toSubarray, Array.start_toSubarray]
  have hvalid := (isValidIndApp?_some h).2
  have harity := isValidIndAppIdx.arity hvalid
  omega

namespace mkRecInfos.loopUArgs

end mkRecInfos.loopUArgs

/-- Exact concrete syntax of one recursive call generated for an argument
selected by `loopCtorArgs`. -/
def GeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (field value : Expr) : Prop :=
  ∃ (exposedType : Expr) (localArgs : Array Expr) (lctx : LocalContext),
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
      minors
    value = (lctx.mkLambda localArgs <|
      (mkAppN (.bvar localArgs.size) indices).app
        (mkAppN field localArgs)).instantiate1 recursor

/-- Prefix invariant for the generated recursive calls: generated values correspond
pointwise to the selected recursive fields. -/
structure GeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    GeneratedRecursiveCall indTypes stats motives minors lvls u[i]
      v[i]!

theorem GeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) (u : Array Expr) :
    GeneratedRecursiveCalls indTypes stats motives minors lvls u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

/-- A validated concrete parameter argument translates to the corresponding
abstract de Bruijn parameter.  The fvar-shape invariant is what upgrades
structural `Expr` equality to exact syntax translation here. -/
theorem ValidAppStatsWF.translatedParam
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlen := List.Forall₂.length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlen, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := forall₂_get?_eq_some hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/- Absence of a newly declared constant is preserved by syntax translation.
Literal expansion and projection translation are explicit side conditions:
literals introduce base primitive constants, and the projection case carries a separate
typing judgment. -/

/- `Expr.AvoidsConsts` (source-syntax absence of a set of constants) is defined in
`Lean4Lean/Verify/ExprParamUniform.lean`. -/

/-- Closing a free variable cannot introduce a constant name. -/
theorem _root_.Lean.Expr.AvoidsConsts.abstract1
    (H : Lean.Expr.AvoidsConsts names e) (fv : FVarId) (k : Nat := 0) :
    Lean.Expr.AvoidsConsts names (Lean.Expr.abstract1 fv e k) := by
  induction H generalizing k with
  | bvar i => exact Lean.Expr.AvoidsConsts.bvar _
  | fvar other =>
      by_cases h : fv == other
      · simpa [Expr.abstract1, h] using
          (Lean.Expr.AvoidsConsts.bvar k :
            Lean.Expr.AvoidsConsts names (.bvar k))
      · simpa [Expr.abstract1, h] using
          (Lean.Expr.AvoidsConsts.fvar other :
            Lean.Expr.AvoidsConsts names (.fvar other))
  | mvar mv => simpa [Expr.abstract1] using
      (Lean.Expr.AvoidsConsts.mvar mv :
        Lean.Expr.AvoidsConsts names (.mvar mv))
  | sort u => simpa [Expr.abstract1] using
      (Lean.Expr.AvoidsConsts.sort u :
        Lean.Expr.AvoidsConsts names (.sort u))
  | const name levels fresh =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.const name levels fresh
  | app fn arg _ _ ihFn ihArg =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.app _ _
        (ihFn k) (ihArg k)
  | lam name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.lam name _ _ bi
        (ihDom k) (ihBody (k + 1))
  | forallE name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.forallE name _ _ bi
        (ihDom k) (ihBody (k + 1))
  | letE name type value body nondep _ _ _ ihType ihValue ihBody =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.letE name _ _ _
        nondep (ihType k) (ihValue k) (ihBody (k + 1))
  | lit value expanded ih =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.lit value expanded
  | mdata data body _ ih =>
      simpa [Expr.abstract1] using Lean.Expr.AvoidsConsts.mdata data _ (ih k)
  | proj structName idx body _ ih =>
      simpa [Expr.abstract1] using
        Lean.Expr.AvoidsConsts.proj structName idx _ (ih k)

/-- Simultaneous (one-pass) abstraction cannot introduce a constant name. -/
theorem _root_.Lean.Expr.AvoidsConsts.abstractN
    (H : Lean.Expr.AvoidsConsts names e) (fvs : List FVarId) (k : Nat := 0) :
    Lean.Expr.AvoidsConsts names (Lean.Expr.abstractN fvs e k) := by
  induction H generalizing k with
  | bvar i => exact Lean.Expr.AvoidsConsts.bvar _
  | fvar other =>
      simp only [Expr.abstractN]
      split
      · exact Lean.Expr.AvoidsConsts.bvar _
      · exact Lean.Expr.AvoidsConsts.fvar other
  | mvar mv => exact Lean.Expr.AvoidsConsts.mvar mv
  | sort u => exact Lean.Expr.AvoidsConsts.sort u
  | const name levels fresh => exact Lean.Expr.AvoidsConsts.const name levels fresh
  | app fn arg _ _ ihFn ihArg =>
      exact Lean.Expr.AvoidsConsts.app _ _ (ihFn k) (ihArg k)
  | lam name dom body bi _ _ ihDom ihBody =>
      exact Lean.Expr.AvoidsConsts.lam name _ _ bi (ihDom k) (ihBody (k + 1))
  | forallE name dom body bi _ _ ihDom ihBody =>
      exact Lean.Expr.AvoidsConsts.forallE name _ _ bi (ihDom k) (ihBody (k + 1))
  | letE name type value body nondep _ _ _ ihType ihValue ihBody =>
      exact Lean.Expr.AvoidsConsts.letE name _ _ _ nondep (ihType k) (ihValue k) (ihBody (k + 1))
  | lit value expanded _ => exact Lean.Expr.AvoidsConsts.lit value expanded
  | mdata data body _ ih => exact Lean.Expr.AvoidsConsts.mdata data _ (ih k)
  | proj structName idx body _ ih => exact Lean.Expr.AvoidsConsts.proj structName idx _ (ih k)

/-- A translation performed before a fresh constant is installed certifies
that the source syntax itself does not mention that constant.  Unlike
`TrExprS.noFreshConsts`, this fact remains usable when the same source
fragment is translated later in an extended environment. -/
theorem TrExprS.sourceAvoidsFresh
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (H : TrExprS env Us Δ e e') : e.AvoidsConsts names := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | sort => exact .sort _
  | @const name levels _ _ _ hlookup _ _ =>
    apply Lean.Expr.AvoidsConsts.const
    intro hmem
    rw [hfresh name hmem] at hlookup
    cases hlookup
  | app _ _ _ _ ihFn ihArg => exact .app _ _ ihFn ihArg
  | lam _ _ _ ihDom ihBody => exact .lam _ _ _ _ ihDom ihBody
  | forallE _ _ _ _ ihDom ihBody =>
    exact .forallE _ _ _ _ ihDom ihBody
  | letE _ _ _ _ ihType ihValue ihBody =>
    exact .letE _ _ _ _ _ ihType ihValue ihBody
  | lit _ _ ih => exact .lit _ ih
  | mdata _ ih => exact .mdata _ _ ih
  | proj _ _ ih => exact .proj _ _ _ ih

/-- Source-support form of the local-context freshness invariant. -/
def VLCtx.SourceConstFree (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.SourceConstFree names

theorem VLCtx.SourceConstFree.ofNoIndConsts
    (H : VLCtx.NoIndConsts names Δ) :
    VLCtx.SourceConstFree names Δ :=
  fun hfind => VExpr.SourceConstFree.ofContainsAnyConst (H hfind)

theorem VLCtx.SourceConstFree.cons
    (H : VLCtx.SourceConstFree names Δ)
    (hvalue : d.value.SourceConstFree names) :
    VLCtx.SourceConstFree names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    exact (H hfind).liftN d.depth 0

/-- When the translation is retained at the checking boundary, ordinary target
well-formedness proves freshness for the whole translated expression,
including projection targets. -/
theorem TrExprS.noFreshConstsAtCheckingEnv
    (henv : VEnv.OrderedStrong env)
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.WF env Us.length Delta)
    (H : TrExprS env Us Delta expression target) :
    target.containsAnyConst names = false :=
  VExpr.WF.noFreshConsts henv hfresh hctx.toCtx (H.wf henv hctx)

theorem TrExprS.noIndOccAvailable
    (halign : IndConstNames indConsts names)
    (hlit : AvailableLiteralDisjoint env indConsts)
    (hctx : VLCtx.NoIndConsts names Δ)
    (H : TrExprS env Us Δ e e')
    (hno : AddInductive.hasIndOcc indConsts e = false) :
    e'.SourceConstFree names := by
  have hctxSupport : VLCtx.SourceConstFree names Δ :=
    VLCtx.SourceConstFree.ofNoIndConsts hctx
  clear hctx
  rw [hasIndOcc_eq_findAny] at hno
  induction H with
  | bvar hfind | fvar hfind =>
    exact hctxSupport hfind
  | sort _ => exact .sort _
  | @const name levels _ _ _ _ _ _ =>
    simp only [Expr.findAny] at hno
    apply VExpr.SourceConstFree.const
    intro hname
    have : names.contains name = true := by simpa using hname
    rw [← halign] at this
    rw [this] at hno
    cases hno
  | app _ _ _ _ ihFn ihArg =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hfn, harg⟩
    exact .app (ihFn hfn hctxSupport) (ihArg harg hctxSupport)
  | lam _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply VExpr.SourceConstFree.lam (ihTy hty hctxSupport)
    apply ihBody hbody
    exact VLCtx.SourceConstFree.cons (d := .vlam _) (ofv := none)
      hctxSupport (.bvar 0)
  | forallE _ _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply VExpr.SourceConstFree.forallE (ihTy hty hctxSupport)
    apply ihBody hbody
    exact VLCtx.SourceConstFree.cons (d := .vlam _) (ofv := none)
      hctxSupport (.bvar 0)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨htyValue, hbody⟩
    rcases Bool.or_eq_false_iff.mp htyValue with ⟨hty, hvalue⟩
    have hvalue' := ihValue hvalue hctxSupport
    exact ihBody hbody (VLCtx.SourceConstFree.cons
      (d := .vlet _ _) (ofv := none) hctxSupport hvalue')
  | lit hcontains _ ih =>
    apply ih
    rw [← hasIndOcc_eq_findAny]
    exact hlit _ hcontains
    exact hctxSupport
  | mdata _ ih =>
    simpa only [Expr.findAny, Bool.false_or] using ih hno hctxSupport
  | proj _ Hproj ih =>
    simp only [Expr.findAny, Bool.false_or] at hno
    cases Hproj
    exact .proj _ _ (ih hno hctxSupport)

theorem ValidAppStatsWF.translatedIndexNoOccurrence
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hlit : AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].SourceConstFree (decl.types.map (·.name)) := by
  have hlen := List.Forall₂.length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlen]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := forall₂_get?_eq_some hargs hsource htarget
  have hno := isValidIndAppIdx.indexNoOccurrence hvalid hlower hjArgs
  exact TrExprS.noIndOccAvailable H.consts.names hlit hctx harg hno

theorem isValidIndAppIdx.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (htarget : target = none ∨ target = some decl.types[typeIdx].name)
    (hlit : AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ) :
    decl.ValidIndAppAt target depth type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlen := List.mapM_some_length hlevels
    have hstats := H.levels
    omega
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := List.Forall₂.length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalid hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, htarget,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalid hargs hlit hctx
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

/-- The exact indexed target recognized by the executable checker is a type,
not merely a well-typed term.  Header shape supplies the forall-to-sort
telescope; the syntax translation supplies all argument and universe typing. -/
theorem isValidIndAppIdx.isType
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (huvars : decl.types[typeIdx].uvars = decl.uvars)
    (hlookup : env.constants decl.types[typeIdx].name =
      some decl.types[typeIdx].toVConstant)
    (htargetWF : decl.types[typeIdx].toVConstant.WF env)
    (hshape : decl.TypeShape env params decl.types[typeIdx])
    (henv : env.WF) (hΔ : Δ.WF env Us.length) :
    env.IsType Us.length Δ.toCtx type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels, args, hspine, hlevels, _hargs⟩
  have hlevelsWF : ∀ level ∈ levels, level.WF Us.length :=
    VLevel.WF.of_mapM_ofLevel hlevels
  have hlevelsLength : levels.length = decl.types[typeIdx].uvars := by
    have htranslated := List.mapM_some_length hlevels
    have hstats := H.levels
    rw [huvars]
    omega
  have hargsLength : args.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := List.Forall₂.length_eq _hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  rcases Lean4Lean.VerifyInductive.typeShape_forallAritySort
      huvars henv htargetWF hshape with
    ⟨functionType, typeLevel, hfunctionType, hfunctionShape⟩
  have hfunctionTypeInst := hfunctionType.instL hlevelsWF
  have hconstType : env.HasType Us.length Δ.toCtx
      (.const decl.types[typeIdx].name levels)
      (functionType.instL levels) := by
    have hconstBase := VEnv.HasType.const (Γ := Δ.toCtx) hlookup
      hlevelsWF hlevelsLength
    have hfunctionTypeInst' : env.IsDefEq Us.length []
        (decl.types[typeIdx].type.instL levels)
        (functionType.instL levels) (VExpr.sort (typeLevel.inst levels)) := by
      simpa [VExpr.instL] using hfunctionTypeInst
    exact (hfunctionTypeInst'.weak0 henv.ordered).defeq hconstBase
  have hrebuild := VExpr.mkApps_getAppFnArgs type'
  rw [hspine] at hrebuild
  have happWF : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps (.const decl.types[typeIdx].name levels) args) := by
    rw [hrebuild]
    exact htr.wf henv.orderedStrong hΔ
  have hshapeInst := hfunctionShape.instL levels
  have hshapeInst' : VExpr.ForallAritySort args.length
      (functionType.instL levels) := by
    rw [hargsLength]
    exact hshapeInst
  have hresult := VEnv.HasType.mkApps_isType henv hΔ.toCtx
    hconstType hshapeInst' happWF
  rwa [hrebuild] at hresult

theorem isValidIndApp?.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ) :
    decl.ValidIndAppAt none depth type' := by
  rcases isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  exact isValidIndAppIdx.validIndAppAt H hi' htr hvalidIdx
    (Or.inl rfl) hlit hctx

theorem noOccurrence.WF
    {type : Expr} {Q : Bool → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok false).WF Q
  exact Except.WF.pure hQ

/-- The successful fast path of executable positivity establishes the
declarative nonrecursive case.  All non-syntactic correspondence assumptions
are named at the boundary: the accumulated mutual constants, local-variable
translation, literal expansion, and projection translation. -/
theorem noOccurrence.refines
    {decl : VInductDecl} {type' : VExpr} {depth : Nat} {ctx : List VExpr}
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (htr : TrExprS env Us Δ type type')
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact noOccurrence.WF
    (Q := fun _ => decl.SyntacticallyPositive env ctx depth type')
    hocc (.nonrecursive <|
      checkPositivityStep.TrExprS.noIndOccAvailable hconsts.names hlit hctx
        htr hocc)

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q true) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

/-- Once the application-spine refinement supplies `ValidIndAppAt`, the final
executable success branch is exactly the declarative recursive positivity
constructor. -/
theorem validApplication.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hrefines : decl.ValidIndAppAt none depth type') :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact validApplication.WF hocc hforall hvalid (.recursive hrefines)

theorem validApplication.sourceRefines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  apply validApplication.refines hocc hforall hvalid
  exact isValidIndApp?.validIndAppAt Hstats htr hvalid hlit hctx

theorem invalidApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = none) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

theorem negativeDomain.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_pos hdomOcc]
  change (Except.error _).WF Q
  exact Except.WF.throw

/-- Positive higher-order branch after WHNF.  Source-domain annotation
transport is shared with header and constructor telescopes. -/
theorem forallE.sourceWF
    (Hc : ContextWF c)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ body₀'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom₀ :: Hc.chk.vlctx.toCtx) sourceBody₀ body₀'' →
      TrExprS Hc.venv c.lparams
        (Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      TrExprS Hc.venv c.lparams
        (Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body₀'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_neg (by simp [hdomOcc])]
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  rcases Hdom₀.body Hc.atCheckLCtx hbody₀ with ⟨body₀'', hbody₀'', hbodyEq₀⟩
  refine withCheckedLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => recur (body.instantiate1 arg))
    Hc Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    Hdom.unannotated Hdom.isType hbody''
  have hopened₀ := Hc.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
    Hdom₀.unannotated Hdom₀.isType hbody₀''
  exact Hrec body'' hbodyEq body₀'' hbodyEq₀ hopened hopened₀


end checkPositivityStep

namespace checkConstructors.loopCtor

/-- The terminal constructor target check discharges the declarative
`CtorTailWF.result` rule. -/
theorem result.refines
    {decl : VInductDecl} {depth : Nat} {result type' exprType : VExpr}
    {ctorCtx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hdefeq : env.IsDefEq decl.uvars ctorCtx result type' exprType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF env decl.types[targetIdx]
        ctorCtx depth result) := by
  exact checkConstructors.loopCtor.result.WF
    (Q := fun _ => decl.CtorTailWF env decl.types[targetIdx]
      ctorCtx depth result)
    hforall hvalid (.result
      (checkPositivityStep.isValidIndAppIdx.validIndAppAt
        Hstats hi htr hvalid (Or.inr rfl) hlit hctx)
      hdefeq)


end checkConstructors.loopCtor

namespace checkPositivity.loop

theorem zero.WF :
    (AddInductive.checkPositivity.loop stats ctor idx type 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkPositivity.loop] at h


/-- Positivity's WHNF step with the concrete free-variable preservation fact
retained for refinements whose semantic scope is narrower than the executable
local context. -/
theorem succ.scopeWF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (htype₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx type type₀)
    (Hstep : ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      FVarsBelow Hc.chk.vlctx type normalized →
      TrExpr Hc.venv c.lparams Hc.chk.vlctx normalized type₀ →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.dualWF Hc htype htype₀).bind
    fun normalized ⟨⟨h1, h2⟩, h3, h4⟩ => Hstep normalized h1 h2 h3 h4


/-- Positivity refinement for constructor checking after mutual headers have
left ambient declarations in the executable context.  The concrete checker
runs in `Hc.mlctx.vlctx`, while every declarative judgment is constructed in
the independent `scope`; runtime WHNF results are restricted before any
positivity rule is emitted. -/
theorem refinesScoped
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    have henv := Hc.checking.tr.wf
    rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceTarget⟩
    obtain ⟨type₀, htype₀, _⟩ := htypeNarrow.alignTo henv halign
    refine succ.scopeWF Hc hsourceFull htype₀ ?_
    intro normalized hbelow hnormalized _hbelow₀ hnormalized₀
    have hnormalizedFVars : FVarsIn (· ∈ scope.fvars) normalized :=
      hbelow _ Hruntime.upset htypeNarrow.fvarsIn
    rcases hnormalized with
      ⟨exposedFull, hexposedFull, _hexposedTarget⟩
    rcases TrExpr.alignBack henv halign htypeNarrow htype₀ hnormalized₀ with
      ⟨exposed, hexposed, hexposedEq⟩
    rcases hexposedEq.symm with ⟨exprType, htypeExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv scope.toCtx depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv scope.toCtx depth narrowType) :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using htypeExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit
        (Hruntime.noIndConsts (decl.types.map (·.name))) hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hexposedFull with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases halign.forallE_align henv hdomNarrow hdomNarrowType hbodyNarrow with
            ⟨dom₀, body₀, hdom₀, hdom₀Type, hdomU, hbody₀, _⟩
          rcases hconsume _ Hc.atCheckLCtx hdom₀ hdom₀Type with
            ⟨consumedDom₀, Hdom₀⟩
          refine finish <| checkPositivityStep.forallE.sourceWF
            (Q := fun _ => decl.SyntacticallyPositive Hc.venv
              scope.toCtx depth (.forallE _ _))
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull Hdom₀ hbody₀ ?_
          intro bodyFull' _hbodyFullEq body₀' _hbody₀Eq hopenedFull _hopened₀
          let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
          have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.unannotatedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.FrontScopeEmbedding
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
              hdomNarrow hdomain hdomNarrowType
          -- the checking-scope domain against the checker's unannotated domain
          have hscopeΓ := halign.wf.toCtx
          have hctxSym := halign.defeqCtx.symm henv.ordered
          rcases Hdom₀.source_defeq with ⟨u₀, hsc₀⟩
          have hsc₀' := hsc₀.defeqDFC henv.ordered hctxSym
          have hdomC : Hc.venv.IsDefEqU c.lparams.length scope.toCtx
              narrowDom consumedDom₀ :=
            hdomU.trans henv hscopeΓ ⟨_, hsc₀'⟩
          rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
          have hfresh : (⟨c.ngen.curr⟩ : FVarId) ∉ scope.fvars := by
            intro hmem
            rw [halign.fvars] at hmem
            exact Hc.current_not_mem (Hc.check.embed.fvars_subset hmem)
          have halign' : VLCtx.IsDefEq Hc'.venv c.lparams.length
              ((some (⟨c.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                .vlam narrowDom) :: scope) Hc'.chk.vlctx :=
            halign.consAligned hfresh hdeps
              (hdomC.of_l henv hscopeΓ hdomTyped)
          have hscopeWF := halign'.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have Hrec := ih Hc' Hruntime' halign' Hstats' hlit hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ hpositive => by
            rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
            change Hc.venv.IsDefEq c.lparams.length scope.toCtx
              narrowDom narrowDom (.sort domLevel) at hdomTyped
            change Hc.venv.IsDefEq c.lparams.length
              (narrowDom :: scope.toCtx) narrowBody narrowBody
              (.sort bodyLevel) at hbodyTyped
            exact .forallE
              (checkPositivityStep.TrExprS.noIndOccAvailable Hstats.consts.names
                hlit (Hruntime.noIndConsts (decl.types.map (·.name)))
                hdomNarrow hdomOcc')
              (by simpa [Hstats.uvars] using hdomTyped)
              (by simpa [Hstats.uvars] using hbodyTyped)
              hpositive
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit
            (Hruntime.noIndConsts (decl.types.map (·.name)))
            hocc' hforall hvalid

end checkPositivity.loop

theorem checkPositivity.WF
    (Hloop : (AddInductive.checkPositivity.loop stats ctor idx type
      c.fuel.inductiveFuel c).WF Q) :
    (AddInductive.checkPositivity stats type ctor idx c).WF Q := by
  unfold AddInductive.checkPositivity
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact Hloop


/-- Public checking-scope positivity refinement, including the executable's fuel
lookup used by constructor checking. -/
theorem checkPositivity.refinesScoped
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refinesScoped Hc Hruntime halign Hstats hconsume
    hlit htypeNarrow htypeFull


end VerifyInductive
end Lean4Lean
