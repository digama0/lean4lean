import Lean4Lean.Verify.Inductive.Recursor.Installation

/-! Identical concrete forall prefixes (`Expr.SameForallPrefix`) and the closing of two bodies
over the same local selection (`CDeclArray.sameForallPrefix`); source branch:
`Nested/Restoration/ParameterOpening.lean`, used by the rule typing. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- In a well-formed local context, a declaration occurring in `toList` is
the unique declaration found at its free-variable identifier. -/
theorem LocalContextWF_find?_eq_some_of_mem
    {lctx : LocalContext} {d : LocalDecl}
    (H : lctx.WF) (hd : d ∈ lctx.toList) :
    lctx.find? d.fvarId = some d := by
  rw [H.find?_eq_find?_toList]
  have find_of_nodup : ∀ (ds : List LocalDecl) (d : LocalDecl),
      (ds.map (fun decl => decl.fvarId)).Nodup → d ∈ ds →
      ds.find? (d.fvarId == ·.fvarId) = some d := by
    intro ds
    induction ds with
    | nil => simp
    | cons head tail ih =>
      intro d hnodup hmem
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp
      · have hne : d.fvarId ≠ head.fvarId := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨d, hmem, rfl⟩)
        simp [hne, ih d hnodup.2 hmem]
  exact find_of_nodup lctx.toList d H.nodup hd


/-- A positional free-variable declaration (`FVarDeclAt`) and a declaration occurring at the
same free-variable identifier in a well-formed context are the same local
declaration. -/
theorem FVarDeclAt.declaration_eq_of_mem
    (D : FVarDeclAt c xs i)
    (Hc : BindingContextWF c)
    (d : LocalDecl) (hd : d ∈ c.lctx.toList)
    (hfv : d.fvarId = D.fvar) :
    d = .cdecl D.index D.fvar D.userName D.type D.binderInfo D.kind := by
  have hfind := LocalContextWF_find?_eq_some_of_mem Hc.wf hd
  rw [hfv] at hfind
  exact Option.some.inj (hfind.symm.trans D.declaration)



/-- Two expressions have the same concrete leading forall binders, while
their residual bodies may differ.  This is the exact syntactic relation
between a source constructor and its nested-lowered constructor. -/
inductive Expr.SameForallPrefix : Nat → Expr → Expr → Prop
  | nil : Expr.SameForallPrefix 0 left right
  | cons : Expr.SameForallPrefix n left right →
      Expr.SameForallPrefix (n + 1)
        (.forallE name dom left bi) (.forallE name dom right bi)

theorem Expr.SameForallPrefix.symm
    (H : Expr.SameForallPrefix n left right) :
    Expr.SameForallPrefix n right left := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem Expr.SameForallPrefix.trans
    (H₁ : Expr.SameForallPrefix n left middle)
    (H₂ : Expr.SameForallPrefix n middle right) :
    Expr.SameForallPrefix n left right := by
  induction H₁ generalizing right with
  | nil => cases H₂; exact .nil
  | cons _ ih =>
    cases H₂ with
    | cons H₂ => exact .cons (ih H₂)

/-- The common concrete binder domains of two forall telescopes transfer a
free-variable bound from the right telescope to the left once the left
residual satisfies that same bound.  This is useful when replay identifies
the binder prefix but the two passes deliberately build different result
expressions. -/
theorem Expr.SameForallPrefix.leftFVarsIn
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (HrightScope : right.FVarsIn P)
    (HleftResidualScope : leftResidual.FVarsIn P) :
    left.FVarsIn P := by
  induction H generalizing leftResidual with
  | nil =>
    cases Hleft
    exact HleftResidualScope
  | cons _ ih =>
    cases Hleft with
    | cons Hleft =>
      exact ⟨HrightScope.1,
        ih Hleft HrightScope.2 HleftResidualScope⟩

/-- Closedness obeys the same prefix transfer principle.  The residual is
checked beneath the complete prefix, while every shared binder domain is
read from the closed right telescope. -/
theorem Expr.SameForallPrefix.leftClosed
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (HrightClosed : Closed right k)
    (HleftResidualClosed : Closed leftResidual (k + n)) :
    Closed left k := by
  induction H generalizing leftResidual k with
  | nil =>
    cases Hleft
    simpa using HleftResidualClosed
  | @cons n left right name dom bi H ih =>
    cases Hleft with
    | cons Hleft =>
      refine ⟨HrightClosed.1, ih Hleft HrightClosed.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        HleftResidualClosed

/-- Identical concrete forall prefixes are complete once their residual
bodies are identified.  Keeping both telescope witnesses explicit avoids
relying on a syntactic `isForall` loop when the prefix was produced by two
independent executable passes. -/
theorem Expr.SameForallPrefix.eq_of_residual_eq
    (H : Expr.SameForallPrefix n left right)
    (Hleft : Expr.ForallTelescope left n leftResidual)
    (Hright : Expr.ForallTelescope right n rightResidual)
    (hresidual : leftResidual = rightResidual) :
    left = right := by
  induction H generalizing leftResidual rightResidual with
  | nil =>
    cases Hleft
    cases Hright
    exact hresidual
  | cons _ ih =>
    cases Hleft with
    | cons Hleft =>
      cases Hright with
      | cons Hright =>
        exact congrArg
          (fun body => Expr.forallE _ _ body _)
          (ih Hleft Hright hresidual)

/-- Reuse the binder-domain part of one translated forall telescope with a
different residual.  This is the dependent-type counterpart of
`SameLambdaPrefix.replaceTranslatedResidual`: the template supplies the
exact translated domains, while an independently translated and well-formed
residual supplies the new codomain. -/
theorem Expr.SameForallPrefix.replaceTranslatedResidual
    (Hsame : Expr.SameForallPrefix n template replacement)
    (HtemplateTelescope : Expr.ForallTelescope template n templateResidual)
    (HreplacementTelescope :
      Expr.ForallTelescope replacement n replacementResidual)
    (henv : VEnv.WF env)
    (Hctx : OnCtx Delta.toCtx (env.IsType Us.length))
    (hdomains : domains.length = n)
    (Htemplate : TrExprS env Us Delta template
      (VExpr.wrapForalls domains templateTarget))
    (HreplacementResidual :
      TrExprS env Us (abstractForallContext domains Delta)
        replacementResidual replacementTarget)
    (HreplacementResidualType : env.IsType Us.length
      (abstractForallContext domains Delta).toCtx replacementTarget) :
    TrExprS env Us Delta replacement
      (VExpr.wrapForalls domains replacementTarget) := by
  induction Hsame generalizing domains Delta templateResidual
      replacementResidual templateTarget replacementTarget with
  | nil =>
    cases HtemplateTelescope
    cases HreplacementTelescope
    have hnil : domains = [] := List.eq_nil_of_length_eq_zero hdomains
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using
      HreplacementResidual
  | @cons n left right name dom bi Hsame ih =>
    cases HtemplateTelescope with
    | cons HtemplateTail =>
      cases HreplacementTelescope with
      | cons HreplacementTail =>
        cases domains with
        | nil => simp at hdomains
        | cons domain domains =>
          cases Htemplate with
          | forallE HdomainType HtemplateBodyType HdomainTr HtemplateBody =>
            have htail : domains.length = n := by simpa using hdomains
            have Hctx' : OnCtx (domain :: Delta.toCtx)
                (env.IsType Us.length) := ⟨Hctx, HdomainType⟩
            have Hopened := VEnv.IsType.wrapForalls_inv henv.ordered Hctx'
              HtemplateBodyType
            have HreplacementResidualType' : env.IsType Us.length
                (domains.reverse ++ domain :: Delta.toCtx)
                replacementTarget := by
              rw [abstractForallContext_toCtx] at HreplacementResidualType
              simpa [VLCtx.toCtx] using HreplacementResidualType
            have HreplacementBodyType : env.IsType Us.length
                (domain :: Delta.toCtx)
                (VExpr.wrapForalls domains replacementTarget) :=
              VEnv.IsType.wrapForalls Hopened.1
                HreplacementResidualType'
            apply TrExprS.forallE HdomainType HreplacementBodyType HdomainTr
            simpa [abstractForallContext, List.map_append,
              List.append_assoc] using
              ih HtemplateTail HreplacementTail
                (by simpa [VLCtx.toCtx] using Hctx') htail HtemplateBody
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidual)
                (by simpa [abstractForallContext, List.map_append,
                    List.append_assoc] using HreplacementResidualType)

theorem Expr.SameForallPrefix.instantiate1'
    (H : Expr.SameForallPrefix n left right) (arg : Expr) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.instantiate1' arg k) (right.instantiate1' arg k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.instantiate1']
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstract1
    (H : Expr.SameForallPrefix n left right) (fv : FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstract1 fv k) (right.abstract1 fv k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstract1]
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstractN
    (H : Expr.SameForallPrefix n left right) (xs : List FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstractN xs k) (right.abstractN xs k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.abstractN]
    exact .cons (ih (k + 1))

theorem Expr.SameForallPrefix.abstractList
    (H : Expr.SameForallPrefix n left right)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.SameForallPrefix n
      (left.abstractList fvars k) (right.abstractList fvars k) := by
  induction fvars generalizing left right k with
  | nil => simpa using H
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

theorem Expr.SameForallPrefix.liftLooseBVars'
    (H : Expr.SameForallPrefix n left right)
    (s amount : Nat) :
    Expr.SameForallPrefix n
      (left.liftLooseBVars' s amount) (right.liftLooseBVars' s amount) := by
  induction H generalizing s with
  | nil => exact .nil
  | cons H ih =>
    simp only [Expr.liftLooseBVars']
    exact .cons (ih (s + 1))

theorem Expr.SameForallPrefix.target_isForall_of_pos
    (H : Expr.SameForallPrefix n source target) (hpos : 0 < n) :
    target.isForall = true := by
  cases H with
  | nil => simp at hpos
  | cons => rfl

/-- Translating two concrete telescopes with an identical forall prefix
produces definitionally equal abstract binder contexts.  Their residual
bodies need not agree: only the shared concrete domain at each layer is
compared, in the context conversion accumulated from the preceding layers. -/
theorem Expr.SameForallPrefix.translatedContexts
    (H : Expr.SameForallPrefix n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left leftTarget)
    (Hright : TrExprS env Us rightCtx right rightTarget) :
    ∃ leftDomains leftResidual rightDomains rightResidual,
      leftDomains.length = n ∧
      rightDomains.length = n ∧
      leftTarget = VExpr.wrapForalls leftDomains leftResidual ∧
      rightTarget = VExpr.wrapForalls rightDomains rightResidual ∧
      VEnv.IsDefEqCtx env Us.length []
        (leftDomains.reverse ++ leftCtx.toCtx)
        (rightDomains.reverse ++ rightCtx.toCtx) := by
  induction H generalizing leftCtx rightCtx leftTarget rightTarget with
  | nil =>
    exact ⟨[], leftTarget, [], rightTarget, rfl, rfl, rfl, rfl, by
      simpa using hctx.defeqCtx⟩
  | @cons n left right name dom bi H ih =>
    cases Hleft with
    | @forallE leftDom leftBody _ _ _ _ _ HleftDomType HleftBodyType
        HleftDom HleftBody =>
      cases Hright with
      | @forallE rightDom rightBody _ _ _ _ _ HrightDomType
          HrightBodyType HrightDom HrightBody =>
        have hdomU := HleftDom.uniq henv hctx HrightDom
        rcases HleftDomType with ⟨_leftLevel, HleftDomType⟩
        have hdom := hdomU.of_l henv hctx.wf.toCtx HleftDomType
        have hctx' : VLCtx.IsDefEq env Us.length
            ((none, .vlam leftDom) :: leftCtx)
            ((none, .vlam rightDom) :: rightCtx) :=
          .cons hctx nofun (.vlam hdom)
        rcases ih hctx' HleftBody HrightBody with
          ⟨leftTail, leftResidual, rightTail, rightResidual,
            hleftLength, hrightLength, hleftTarget, hrightTarget,
            hcontexts⟩
        refine ⟨leftDom :: leftTail, leftResidual,
          rightDom :: rightTail, rightResidual, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hleftLength]
        · simp [hrightLength]
        · simp [VExpr.wrapForalls, hleftTarget]
        · simp [VExpr.wrapForalls, hrightTarget]
        · simpa [List.reverse_cons, List.append_assoc,
            VLCtx.toCtx] using hcontexts

/-- Exact-domain form of `translatedContexts`.  When the two translated
targets have already been decomposed into caller-selected forall domains,
the anonymous context conversion can be returned over those very lists
rather than over fresh existential decompositions of the same targets. -/
theorem Expr.SameForallPrefix.translatedContextsExact
    (H : Expr.SameForallPrefix n left right)
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length leftCtx rightCtx)
    (Hleft : TrExprS env Us leftCtx left
      (VExpr.wrapForalls leftDomains leftResidual))
    (Hright : TrExprS env Us rightCtx right
      (VExpr.wrapForalls rightDomains rightResidual))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n) :
    VEnv.IsDefEqCtx env Us.length []
      (leftDomains.reverse ++ leftCtx.toCtx)
      (rightDomains.reverse ++ rightCtx.toCtx) := by
  rcases H.translatedContexts henv hctx Hleft Hright with
    ⟨actualLeftDomains, actualLeftResidual,
      actualRightDomains, actualRightResidual,
      hactualLeftLength, hactualRightLength,
      hleftTarget, hrightTarget, Hcontexts⟩
  have hleftDomains : leftDomains = actualLeftDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hleftLength hactualLeftLength (by simpa using hleftTarget)
  have hrightDomains : rightDomains = actualRightDomains :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hrightLength hactualRightLength (by simpa using hrightTarget)
  subst actualLeftDomains
  subst actualRightDomains
  exact Hcontexts

/-- Two translated forall telescopes with the same concrete prefix and the same
residual source are definitionally equal, at a sort level, so that a dependent
context conversion can be extended by the resulting domain. -/
theorem Expr.SameForallPrefix.translatedWholeTargetsOfResidualRightSort
    (H : Expr.SameForallPrefix n leftSource rightSource)
    (henv : VEnv.WF env)
    (Hbase : VEnv.IsDefEqCtx env Us.length []
      baseLeft.reverse baseRight.reverse)
    (Hleft : TrExprS env Us
      (abstractForallContext baseLeft []) leftSource
      (VExpr.wrapForalls leftDomains leftTarget))
    (Hright : TrExprS env Us
      (abstractForallContext baseRight []) rightSource
      (VExpr.wrapForalls rightDomains rightTarget))
    (hleftLength : leftDomains.length = n)
    (hrightLength : rightDomains.length = n)
    (HleftResidual : TrExprS env Us
      (abstractForallContext (baseLeft ++ leftDomains) []) residualSource
      leftTarget)
    (HrightResidual : TrExprS env Us
      (abstractForallContext (baseRight ++ rightDomains) []) residualSource
      rightTarget)
    (HrightResidualType : env.IsType Us.length
      (abstractForallContext (baseRight ++ rightDomains) []).toCtx
      rightTarget) :
    ∃ level, env.IsDefEq Us.length baseLeft.reverse
      (VExpr.wrapForalls leftDomains leftTarget)
      (VExpr.wrapForalls rightDomains rightTarget) (.sort level) := by
  have HbaseV := abstractForallContext.isDefEq Hbase
  have Hlocals := H.translatedContextsExact henv HbaseV Hleft Hright
    hleftLength hrightLength
  have Hlocals' : VEnv.IsDefEqCtx env Us.length []
      (baseLeft ++ leftDomains).reverse
      (baseRight ++ rightDomains).reverse := by
    simpa [List.reverse_append, VLCtx.toCtx] using Hlocals
  have HresidualU := TrExprS.uniqAbstractForallContext
    HleftResidual HrightResidual henv Hlocals'
  rcases HrightResidualType with ⟨residualLevel, HrightResidualType⟩
  have HrightResidualType' : env.HasType Us.length
      (baseRight ++ rightDomains).reverse rightTarget
      (.sort residualLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      HrightResidualType
  have HrightResidualTypeLeft : env.HasType Us.length
      (baseLeft ++ leftDomains).reverse rightTarget
      (.sort residualLevel) :=
    HrightResidualType'.defeqDFC henv.ordered
      (Hlocals'.symm henv.ordered)
  have Hresidual : env.IsDefEq Us.length
      (baseLeft ++ leftDomains).reverse leftTarget rightTarget
      (.sort residualLevel) :=
    HresidualU.of_r henv Hlocals'.isType HrightResidualTypeLeft
  have Hclosed :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hlocals'
      n (by simp [hleftLength]) Hresidual
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  exact ⟨closedLevel, by
    simpa [hleftLength, hrightLength] using Hclosed⟩

/-- Closing two residual bodies with the same ordinary declarations creates
the same concrete forall prefix around both. -/
theorem LocalContext.sameForallPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (left right : Expr) :
    Expr.SameForallPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) left)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) right) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameForallPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- Closing two bodies over the same duplicate-free local selection gives
the same concrete forall prefix, independently of the bodies. -/
theorem CDeclArray.sameForallPrefix
    (H : CDeclArray lctx xs)
    (hnodup : H.fvars.Nodup) (left right : Expr) :
    Expr.SameForallPrefix xs.size
      (lctx.mkForall xs left) (lctx.mkForall xs right) := by
  rcases H with ⟨fvars, rfl, hdecl⟩
  have hfind : ∀ fv ∈ fvars, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    rcases hdecl fv hfv with ⟨index, name, type, bi, kind, hfound⟩
    exact ⟨.cdecl index fv name type bi kind, hfound⟩
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  simpa using LocalContext.sameForallPrefixN_fold hdecl left right


end VerifyInductive
end Lean4Lean
