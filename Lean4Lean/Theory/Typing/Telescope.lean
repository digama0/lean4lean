import Lean4Lean.Theory.VExpr.TelescopeLemmas
import Lean4Lean.Theory.Typing.Injectivity

/-! # Dependent telescope typing

Context insertion and conversion, telescope introduction and inversion, and typed application
spines for the abstract calculus. Existing qualified names are retained for compatibility.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open scoped _root_.List

namespace VerifyInductive

/-- A declaration selected below a newer context prefix is looked up at the
prefix length, with one lift for its own binder and one for every newer
declaration. -/
theorem Lookup.append_zero (newer : List VExpr) (domain : VExpr)
    (older : List VExpr) :
    Lookup (newer ++ domain :: older) newer.length
      (domain.liftN (newer.length + 1) 0) := by
  induction newer with
  | nil => simpa [VExpr.liftN] using (Lookup.zero :
      Lookup (domain :: older) 0 domain.lift)
  | cons head newer ih =>
    simpa [VExpr.liftN_succ, Nat.add_assoc] using
      (Lookup.succ (A := head) ih)

/-- Insert `inserted` below `prefix` and above `suffix`, lifting each
dependent prefix declaration at its exact de Bruijn cutoff. -/
theorem Ctx.LiftN.insertAfterPrefix
    (recent inserted suffix : List VExpr) :
    Ctx.LiftN inserted.length recent.length (recent ++ suffix)
      (liftContextPrefix inserted.length recent ++ inserted ++ suffix) := by
  induction recent with
  | nil =>
    simpa [liftContextPrefix, liftContextPrefixAt, List.append_assoc] using
      (Ctx.LiftN.zero (Γ := suffix) inserted)
  | cons domain recent ih =>
    simpa [liftContextPrefix, liftContextPrefixAt, List.append_assoc] using
      (Ctx.LiftN.succ (A := domain) ih)

/-- A well-formed recent context remains well formed when a separately
well-formed block is inserted beneath it and every recent declaration is
lifted at its dependent cutoff. -/
theorem _root_.Lean4Lean.OnCtx.insertAfterPrefix
    {env : VEnv} {uvars : Nat}
    {recent inserted outer : List VExpr}
    (henv : env.Ordered)
    (Hrecent : OnCtx (recent ++ outer) (env.IsType uvars))
    (Hinserted : OnCtx (inserted ++ outer) (env.IsType uvars)) :
    OnCtx
      (liftContextPrefix inserted.length recent ++ inserted ++ outer)
      (env.IsType uvars) := by
  induction recent with
  | nil => simpa [liftContextPrefix, liftContextPrefixAt] using Hinserted
  | cons domain recent ih =>
    have Hdomain := Hrecent.2.weakN henv
      (Ctx.LiftN.insertAfterPrefix recent inserted outer)
    exact ⟨ih Hrecent.1, by
      simpa [liftContextPrefix, liftContextPrefixAt] using Hdomain⟩

/-- Insert the same well-formed context block beneath two definitionally
equal recent prefixes.  Each dependent prefix declaration is lifted at the
cutoff determined by the older declarations, exactly as in
`Ctx.LiftN.insertAfterPrefix`. -/
theorem VEnv.IsDefEqCtx.insertSameMiddle
    {env : VEnv} {uvars : Nat}
    (henv : env.Ordered)
    (recent₁ recent₂ inserted outer : List VExpr)
    (H : VEnv.IsDefEqCtx env uvars []
      (recent₁ ++ outer) (recent₂ ++ outer))
    (hlength : recent₁.length = recent₂.length)
    (hctx : OnCtx (inserted ++ outer) (env.IsType uvars)) :
    VEnv.IsDefEqCtx env uvars []
      (liftContextPrefix inserted.length recent₁ ++ inserted ++ outer)
      (liftContextPrefix inserted.length recent₂ ++ inserted ++ outer) := by
  induction recent₁ generalizing recent₂ with
  | nil =>
    have hrefl := VEnv.IsDefEqCtx.refl hctx
    have hrecent₂ : recent₂ = [] :=
      List.eq_nil_of_length_eq_zero hlength.symm
    simpa [hrecent₂, liftContextPrefix, liftContextPrefixAt] using hrefl
  | cons domain₁ recent₁ ih =>
    cases recent₂ with
    | nil => simp at hlength
    | cons domain₂ recent₂ =>
      simp only [List.cons_append] at H
      cases H with
      | succ Hprior Hdomain =>
        have htailLength : recent₁.length = recent₂.length := by
          simpa using Nat.succ.inj hlength
        have Hprior' := ih recent₂ Hprior htailLength
        have W := Ctx.LiftN.insertAfterPrefix recent₁ inserted outer
        have Hdomain' := Hdomain.weakN henv W
        exact .succ Hprior' (by
          rw [← htailLength]
          simpa [liftContextPrefix, liftContextPrefixAt, VExpr.liftN] using
            Hdomain')

/-- A nonempty extension of the fixed base context must end in `succ`, so its
outermost declaration and prior conversion can be recovered without treating
the base context itself as a newly added declaration. -/
theorem VEnv.IsDefEqCtx.extensionConsInv
    {env : VEnv} {uvars : Nat} {outer Γ₁ Γ₂ : List VExpr}
    {domain₁ domain₂ : VExpr}
    (H : VEnv.IsDefEqCtx env uvars outer
      (domain₁ :: Γ₁) (domain₂ :: Γ₂))
    (hlength : outer.length < (domain₁ :: Γ₁).length) :
    ∃ level,
      VEnv.IsDefEqCtx env uvars outer Γ₁ Γ₂ ∧
      env.IsDefEq uvars Γ₁ domain₁ domain₂ (.sort level) := by
  cases H with
  | zero => simp at hlength
  | succ Hprior Hdomain => exact ⟨_, Hprior, Hdomain⟩

/-- Close a dependent context conversion back into a definitional equality
of forall telescopes.  `recent₁` and `recent₂` are stored in local-context
order, so reversing them restores source binder order for `wrapForalls`. -/
theorem VEnv.IsDefEqCtx.closeWrapForalls
    {env : VEnv} {uvars : Nat}
    (outer recent₁ recent₂ : List VExpr)
    (H : VEnv.IsDefEqCtx env uvars outer
      (recent₁ ++ outer) (recent₂ ++ outer))
    (Hbody : env.IsDefEq uvars (recent₁ ++ outer)
      body₁ body₂ (.sort bodyLevel)) :
    env.IsDefEqU uvars outer
      (VExpr.wrapForalls recent₁.reverse body₁)
      (VExpr.wrapForalls recent₂.reverse body₂) := by
  induction recent₁ generalizing recent₂ body₁ body₂ bodyLevel with
  | nil =>
    have hrecent₂ : recent₂ = [] := by
      have hlength := H.length_eq
      simp at hlength
      exact hlength
    subst recent₂
    exact ⟨_, by simpa [VExpr.wrapForalls] using Hbody⟩
  | cons domain₁ recent₁ ih =>
    cases recent₂ with
    | nil =>
      have hlength := H.length_eq
      simp at hlength
      omega
    | cons domain₂ recent₂ =>
      rcases
          Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extensionConsInv H (by
            simp
            omega) with
        ⟨domainLevel, Hprior, Hdomain⟩
      have Hclosed := VEnv.IsDefEq.forallEDF Hdomain Hbody
      have Hrest := ih recent₂ Hprior Hclosed
      simpa [List.reverse_cons, VExpr.wrapForalls_append,
        VExpr.wrapForalls] using Hrest

theorem VEnv.IsType.wrapForalls_inv
    {env : VEnv} (henv : env.Ordered)
    (hctx : OnCtx ctx (env.IsType uvars))
    (H : env.IsType uvars ctx (VExpr.wrapForalls domains result)) :
    OnCtx (domains.reverse ++ ctx) (env.IsType uvars) ∧
      env.IsType uvars (domains.reverse ++ ctx) result := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapForalls] using And.intro hctx H
  | cons domain domains ih =>
    have hinv := H.forallE_inv henv
    have hctx' : OnCtx (domain :: ctx) (env.IsType uvars) :=
      ⟨hctx, hinv.1⟩
    simpa [VExpr.wrapForalls, List.reverse_cons, List.append_assoc] using
      ih hctx' hinv.2

theorem VEnv.IsType.wrapForalls
    {env : VEnv} (hctx : OnCtx (domains.reverse ++ ctx)
      (env.IsType uvars))
    (H : env.IsType uvars (domains.reverse ++ ctx) result) :
    env.IsType uvars ctx (VExpr.wrapForalls domains result) := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (domain :: ctx))
        (env.IsType uvars) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hrest := ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using H)
    have hdomain : env.IsType uvars ctx domain :=
      (OnCtx.of_append hctx').2
    exact VEnv.IsType.forallE hdomain hrest

/-- Closing a term over a semantically well-formed telescope preserves its
typing.  The domains use the source binder order, while typing contexts use
the corresponding most-recent-first order. -/
theorem VEnv.HasType.wrapLams
    {env : VEnv} (hctx : OnCtx (domains.reverse ++ ctx)
      (env.IsType uvars))
    (H : env.HasType uvars (domains.reverse ++ ctx) body typeBody) :
    env.HasType uvars ctx (VExpr.wrapLams domains body)
      (VExpr.wrapForalls domains typeBody) := by
  induction domains generalizing ctx with
  | nil => simpa [VExpr.wrapLams, VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (domain :: ctx))
        (env.IsType uvars) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hrest := ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using H)
    rcases (OnCtx.of_append hctx').2 with ⟨level, hdomain⟩
    simpa [VExpr.wrapLams, VExpr.wrapForalls] using hdomain.lam hrest

/-- Invert a lambda telescope whose type is the corresponding literal forall
telescope.  Strong lambda inversion initially recovers an arbitrary type for
the open body; uniqueness of typing and forall injectivity transport that
body back to the stated dependent residual before the induction continues.

This is the application-facing inverse of `VEnv.HasType.wrapLams`: generated
recursive results are stored closed, while a dependent minor application
needs their exact open typing under the retained local domains. -/
theorem VEnv.HasType.wrapLams_inv
    {env : VEnv} (henv : env.WF)
    (hctx : OnCtx ctx (env.IsType uvars))
    (H : env.HasType uvars ctx (VExpr.wrapLams domains body)
      (VExpr.wrapForalls domains typeBody)) :
    OnCtx (domains.reverse ++ ctx) (env.IsType uvars) ∧
      env.HasType uvars (domains.reverse ++ ctx) body typeBody := by
  induction domains generalizing ctx with
  | nil =>
    simpa [VExpr.wrapLams, VExpr.wrapForalls] using And.intro hctx H
  | cons domain domains ih =>
    have Hlambda : env.HasType uvars ctx
        (.lam domain (VExpr.wrapLams domains body))
        (.forallE domain (VExpr.wrapForalls domains typeBody)) := by
      simpa [VExpr.wrapLams, VExpr.wrapForalls] using H
    rcases Hlambda.lam_inv henv hctx with
      ⟨HdomainType, actualBodyType, HactualBody⟩
    rcases HdomainType with ⟨domainLevel, Hdomain⟩
    have hctx' : OnCtx (domain :: ctx) (env.IsType uvars) :=
      ⟨hctx, ⟨domainLevel, Hdomain⟩⟩
    have HactualLambda : env.HasType uvars ctx
        (.lam domain (VExpr.wrapLams domains body))
        (.forallE domain actualBodyType) :=
      Hdomain.lam HactualBody
    have HfunctionType := Hlambda.uniqU henv hctx HactualLambda
    rcases (VEnv.IsDefEqU.forallE_inv henv hctx HfunctionType).2 with
      ⟨_bodyLevel, HbodyType⟩
    have HstatedBody : env.HasType uvars (domain :: ctx)
        (VExpr.wrapLams domains body)
        (VExpr.wrapForalls domains typeBody) :=
      HbodyType.defeq' HactualBody
    have Hrest := ih hctx' HstatedBody
    simpa [List.reverse_cons, List.append_assoc] using Hrest

/-- Package two equally typed residual bodies as one closed, well-formed
definitional equation.  This is the common specification-side endpoint for
ordinary and restored nested iota equations. -/
theorem VDefEq.wf_of_wrappedBodies
    {env : VEnv} {uvars : Nat} {domains : List VExpr}
    {lhsBody rhsBody typeBody : VExpr}
    (hctx : OnCtx domains.reverse (env.IsType uvars))
    (hlhs : env.HasType uvars domains.reverse lhsBody typeBody)
    (hrhs : env.HasType uvars domains.reverse rhsBody typeBody) :
    ({ uvars := uvars
       lhs := VExpr.wrapLams domains lhsBody
       rhs := VExpr.wrapLams domains rhsBody
       type := VExpr.wrapForalls domains typeBody } : VDefEq).WF env := by
  have hctx' : OnCtx (domains.reverse ++ []) (env.IsType uvars) := by
    simpa using hctx
  exact ⟨VEnv.HasType.wrapLams hctx' (by simpa using hlhs),
    VEnv.HasType.wrapLams hctx' (by simpa using hrhs)⟩

/-- Inject the next domain after two equally long definitionally equal forall
prefixes.  The result is stated in the left prefix context, matching the
checking context built from the family parameters already opened. -/
theorem VEnv.IsDefEqU.wrapForalls_next
    (henv : VEnv.WF env)
    (hctx : OnCtx ctx (env.IsType uvars))
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls left (.forallE leftNext leftBody))
      (VExpr.wrapForalls right (.forallE rightNext rightBody))) :
    ∃ u, env.IsDefEq uvars (left.reverse ++ ctx)
      leftNext rightNext (.sort u) := by
  induction left generalizing right ctx with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa [VExpr.wrapForalls] using
      (VEnv.IsDefEqU.forallE_inv henv hctx H).1
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : OnCtx (leftHead :: ctx) (env.IsType uvars) :=
        ⟨hctx, ⟨headLevel, hhead.hasType.1⟩⟩
      have hnext := ih (right := rightTail) (ctx := leftHead :: ctx)
        hctx' hlength ⟨_, hbody⟩
      simpa [List.reverse_cons, List.append_assoc] using hnext

/-- Invert two equally long definitionally equal forall telescopes into a
conversion between their full binder contexts.  The outer contexts may
already differ definitionally; each newly exposed domain extends that
conversion before the residual telescope is inspected. -/
theorem VEnv.IsDefEqU.wrapForalls_context
    (henv : VEnv.WF env)
    (hctx : VEnv.IsDefEqCtx env uvars [] leftCtx rightCtx)
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars leftCtx
      (VExpr.wrapForalls left leftBody)
      (VExpr.wrapForalls right rightBody)) :
    VEnv.IsDefEqCtx env uvars []
      (left.reverse ++ leftCtx) (right.reverse ++ rightCtx) := by
  induction left generalizing right leftCtx rightCtx leftBody rightBody with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa using hctx
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx.isType H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : VEnv.IsDefEqCtx env uvars []
          (leftHead :: leftCtx) (rightHead :: rightCtx) :=
        .succ hctx hhead
      have hbodyU : env.IsDefEqU uvars (leftHead :: leftCtx)
          (VExpr.wrapForalls leftTail leftBody)
          (VExpr.wrapForalls rightTail rightBody) :=
        ⟨.sort bodyLevel, hbody⟩
      have hrest := ih hctx' hlength hbodyU
      simpa [List.reverse_cons, List.append_assoc] using hrest

/-- Peel two equally long definitionally equal forall telescopes down to
their residual bodies.  The comparison is stated in the context generated by
the left telescope, matching `forallE_inv` and the dependent-context
convention used by the header checker. -/
theorem VEnv.IsDefEqU.wrapForalls_residual
    (henv : VEnv.WF env)
    (hctx : OnCtx ctx (env.IsType uvars))
    (hlen : left.length = right.length)
    (H : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls left leftBody)
      (VExpr.wrapForalls right rightBody)) :
    env.IsDefEqU uvars (left.reverse ++ ctx) leftBody rightBody := by
  induction left generalizing right ctx with
  | nil =>
    have hright : right = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst right
    simpa [VExpr.wrapForalls] using H
  | cons leftHead leftTail ih =>
    cases right with
    | nil => simp at hlen
    | cons rightHead rightTail =>
      have hlength : leftTail.length = rightTail.length := by
        simpa using Nat.succ.inj hlen
      have hinv := VEnv.IsDefEqU.forallE_inv henv hctx H
      rcases hinv.1 with ⟨headLevel, hhead⟩
      rcases hinv.2 with ⟨bodyLevel, hbody⟩
      have hctx' : OnCtx (leftHead :: ctx) (env.IsType uvars) :=
        ⟨hctx, ⟨headLevel, hhead.hasType.1⟩⟩
      have hrest := ih (right := rightTail) (ctx := leftHead :: ctx)
        hctx' hlength ⟨_, hbody⟩
      simpa [List.reverse_cons, List.append_assoc] using hrest

/-- Repeated application syntax retains a well-typed prefix. -/
theorem VExpr.WF.mkApps_fn
    (henv : env.OrderedStrong) (hctx : OnCtx ctx (env.IsType uvars))
    (H : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    VExpr.WF env uvars ctx fn := by
  induction args generalizing fn with
  | nil => simpa [VExpr.mkApps] using H
  | cons arg args ih =>
    have Hprefix := ih (fn := .app fn arg) H
    rcases Hprefix.app_inv henv hctx with ⟨domain, body, hfn, _harg⟩
    exact ⟨_, hfn⟩

/-- Pointwise convertible arguments preserve a well-formed application
spine.  The function heads may themselves merely be definitionally equal;
typing for each successive application is recovered by inversion from the
well-formed left spine. -/
theorem VEnv.IsDefEqU.mkApps
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.IsDefEqU uvars ctx fn₁ fn₂)
    (Hleft : VExpr.WF env uvars ctx (VExpr.mkApps fn₁ args₁))
    (Hargs : List.Forall₂
      (env.IsDefEqU uvars ctx) args₁ args₂) :
    env.IsDefEqU uvars ctx
      (VExpr.mkApps fn₁ args₁) (VExpr.mkApps fn₂ args₂) := by
  induction Hargs generalizing fn₁ fn₂ with
  | nil => simpa [VExpr.mkApps] using Hfn
  | @cons arg₁ arg₂ args₁ args₂ Harg Hargs ih =>
    have Hprefix := VExpr.WF.mkApps_fn henv hctx
      (fn := .app fn₁ arg₁) (args := args₁) Hleft
    rcases Hprefix.app_inv henv hctx with
      ⟨domain, body, HfnType, HargType⟩
    have HprefixEq : env.IsDefEqU uvars ctx
        (.app fn₁ arg₁) (.app fn₂ arg₂) :=
      (VEnv.IsDefEq.appDF (Hfn.of_l henv hctx HfnType)
        (Harg.of_l henv hctx HargType)).toU
    exact ih HprefixEq Hleft

/-- The first argument of a well-typed application spine has the declared
outer domain of the function.  Application inversion may initially recover
a different convertible domain; uniqueness and forall injectivity transport
the argument back to the stated telescope. -/
theorem VEnv.HasType.mkApps_head
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (hfn : env.HasType uvars ctx fn (.forallE domain body))
    (happs : VExpr.WF env uvars ctx
      (VExpr.mkApps fn (arg :: args))) :
    env.HasType uvars ctx arg domain := by
  have hprefix := VExpr.WF.mkApps_fn henv hctx
    (fn := .app fn arg) (args := args) happs
  rcases hprefix.app_inv henv hctx with
    ⟨actualDomain, actualBody, hfnActual, hargActual⟩
  have hfunctionEq := hfn.uniqU henv hctx hfnActual
  have hdomainEq :=
    (VEnv.IsDefEqU.forallE_inv henv hctx hfunctionEq).1
  rcases hdomainEq with ⟨domainLevel, hdomainEq⟩
  exact hdomainEq.defeq' hargActual

/-- A dependently typed application spine.  Each argument is checked against
the current outer forall domain, and the residual type is instantiated before
the rest of the spine is consumed.  This is the induction principle used for
the generated minor's fields followed by its recursive-result arguments. -/
inductive VEnv.TypedApplicationSpine
    (env : VEnv) (uvars : Nat) (ctx : List VExpr) :
    VExpr → VExpr → List VExpr → VExpr → Prop
  | nil (Hfn : env.HasType uvars ctx fn fnType) :
      TypedApplicationSpine env uvars ctx fn fnType [] fnType
  | cons
      (Hfn : env.HasType uvars ctx fn (.forallE domain body))
      (Harg : env.HasType uvars ctx arg domain)
      (Htail : TypedApplicationSpine env uvars ctx
        (.app fn arg) (body.inst arg) args resultType) :
      TypedApplicationSpine env uvars ctx fn (.forallE domain body)
        (arg :: args) resultType

theorem VEnv.TypedApplicationSpine.hasType
    (H : VEnv.TypedApplicationSpine env uvars ctx fn fnType args resultType) :
    env.HasType uvars ctx (VExpr.mkApps fn args) resultType := by
  induction H with
  | nil Hfn => simpa [VExpr.mkApps] using Hfn
  | cons Hfn Harg _ ih =>
      simpa [VExpr.mkApps] using ih

/-- A term whose type is a dependent forall telescope can be weakened beneath
that telescope and applied to the bound variables of all of its binders
(`#(n-1) .. #0`). The result has the residual body type in the context extended by the
telescope. -/
theorem VEnv.HasType.mkApps_wrapForalls_bvarSpine
    {env : VEnv} {uvars : Nat} {ctx : List VExpr} {fn : VExpr}
    {domains : List VExpr} {body : VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.HasType env uvars ctx fn (VExpr.wrapForalls domains body)) :
    VEnv.HasType env uvars (domains.reverse ++ ctx)
      (VExpr.mkApps (fn.liftN domains.length 0)
        ((List.range domains.length).reverse.map .bvar)) body := by
  induction domains generalizing ctx fn with
  | nil => simpa [VExpr.mkApps, VExpr.wrapForalls] using H
  | cons domain domains ih =>
    have hfirst := (H.weakN henv (Ctx.LiftN.one (A := domain))).app
      (VEnv.HasType.bvar Lookup.zero)
    have hfirst' : VEnv.HasType env uvars (domain :: ctx)
        (.app (fn.liftN 1 0) (.bvar 0))
        (VExpr.wrapForalls domains body) := by
      simpa [VExpr.wrapForalls, VExpr.liftN, VExpr.inst_liftN_bvar] using hfirst
    have hrest := ih hfirst'
    simpa [VExpr.wrapForalls, VExpr.mkApps, List.range_succ,
      List.reverse_cons, List.append_assoc, VExpr.liftN,
      VExpr.inst_liftN_bvar, VExpr.liftN_liftN, Nat.add_comm] using hrest

/-- Applying only an initial segment of a dependent telescope leaves the
remaining suffix as the type of the bound-variable partial application. -/
theorem VEnv.HasType.mkApps_wrapForalls_prefix_bvarSpine
    {env : VEnv} {uvars : Nat} {ctx : List VExpr} {fn : VExpr}
    {initial suffix : List VExpr} {body : VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.HasType env uvars ctx fn
      (VExpr.wrapForalls (initial ++ suffix) body)) :
    VEnv.HasType env uvars (initial.reverse ++ ctx)
      (VExpr.mkApps (fn.liftN initial.length 0)
        ((List.range initial.length).reverse.map .bvar))
      (VExpr.wrapForalls suffix body) := by
  rw [VExpr.wrapForalls_append] at H
  exact VEnv.HasType.mkApps_wrapForalls_bvarSpine henv H

/-- A well-formed application of a function whose type is a forall telescope of exactly
`args.length` binders ending in a sort (`VExpr.ForallAritySort`) is a type. -/
theorem VEnv.HasType.mkApps_isType
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (hfn : env.HasType uvars ctx fn fnType)
    (hshape : VExpr.ForallAritySort args.length fnType)
    (happs : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    env.IsType uvars ctx (VExpr.mkApps fn args) := by
  induction args generalizing fn fnType with
  | nil =>
    cases hshape with
    | zero level => exact ⟨level, by simpa [VExpr.mkApps] using hfn⟩
  | cons arg args ih =>
    cases hshape with
    | @succ arity body domain hbody =>
      have hprefix := VExpr.WF.mkApps_fn henv hctx
        (fn := .app fn arg) (args := args) happs
      rcases hprefix.app_inv henv hctx with
        ⟨actualDomain, actualBody, hfnActual, hargActual⟩
      have hfunctionEq := hfn.uniqU henv hctx hfnActual
      have hdomainEq :=
        (VEnv.IsDefEqU.forallE_inv henv hctx hfunctionEq).1
      rcases hdomainEq with ⟨domainLevel, hdomainEq⟩
      have harg : env.HasType uvars ctx arg domain :=
        hdomainEq.defeq' hargActual
      exact ih (fn := .app fn arg) (fnType := body.inst arg)
        (hfn.app harg) (hbody.inst arg) happs

/-- Definitional equality between two equally long dependent function types
survives consumption of the same well-typed argument spine.  The domains may
differ definitionally; `forallE_inv` transports each argument through the
left domain before substituting it into both residuals. -/
theorem VEnv.IsDefEqU.applyForallType
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hshape : SameTelescopeArity args.length leftType rightType)
    (Htypes : env.IsDefEqU uvars ctx leftType rightType)
    (Hleft : env.HasType uvars ctx fn leftType)
    (Happs : VExpr.WF env uvars ctx (VExpr.mkApps fn args)) :
    env.IsDefEqU uvars ctx
      (VExpr.applyForallType leftType args)
      (VExpr.applyForallType rightType args) := by
  induction args generalizing fn leftType rightType with
  | nil =>
    cases Hshape with
    | zero => simpa [VExpr.applyForallType] using Htypes
  | cons arg args ih =>
    cases Hshape with
    | @succ leftDomain rightDomain leftBody rightBody arity Htail =>
      have Harg : env.HasType uvars ctx arg leftDomain :=
        VEnv.HasType.mkApps_head henv hctx Hleft Happs
      rcases (VEnv.IsDefEqU.forallE_inv henv hctx Htypes).2 with
        ⟨bodyLevel, Hbody⟩
      have HbodyInst : env.IsDefEqU uvars ctx
          (leftBody.inst arg) (rightBody.inst arg) := by
        refine ⟨.sort bodyLevel, ?_⟩
        simpa [VExpr.inst] using
          Hbody.instN henv.ordered Harg .zero
      have HleftApp : env.HasType uvars ctx (.app fn arg)
          (leftBody.inst arg) := Hleft.app Harg
      have HappRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app fn arg) args) := by
        simpa [VExpr.mkApps] using Happs
      have Hrest := ih (fn := .app fn arg)
        (Htail.instN arg 0) HbodyInst HleftApp HappRest
      simpa [VExpr.applyForallType] using Hrest

/-- The residual recorded by a typed application spine is the literal
result of consuming its initial forall type with the same arguments.  This
keeps later dependent application proofs from having to existentially forget
the result type they have already computed. -/
theorem VEnv.TypedApplicationSpine.result_eq_applyForallType
    (H : VEnv.TypedApplicationSpine env uvars ctx fn fnType args resultType) :
    resultType = VExpr.applyForallType fnType args := by
  induction H with
  | nil _ => rfl
  | cons _ _ _ ih =>
      simpa [VExpr.applyForallType] using ih

/-- Consume a dependent telescope assembled from independently typed closed
arguments.  This packages the substitution bookkeeping needed by generated
minor hypotheses: after each application, `liftClosedDomains` and
`instForallDomains` reduce the remaining domains back to the same invariant. -/
theorem VEnv.TypedApplicationSpine.liftClosedDomains
    (Hfn : env.HasType uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType))
    (Hargs : List.Forall₂
      (env.HasType uvars ctx) args types) :
    ∃ finalType, VEnv.TypedApplicationSpine env uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType)
      args finalType := by
  induction Hargs generalizing fn resultType with
  | nil =>
    exact ⟨resultType, by
      simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using
        (VEnv.TypedApplicationSpine.nil Hfn)⟩
  | @cons arg domain args types Harg Hargs ih =>
    have Hfn' : env.HasType uvars ctx fn
        (.forallE domain
          (VExpr.wrapForalls (VExpr.liftClosedDomains types 1)
            resultType)) := by
      simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using Hfn
    have Happ := Hfn'.app Harg
    have Happ' : env.HasType uvars ctx (.app fn arg)
        (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
          (resultType.inst arg types.length)) := by
      rw [VExpr.inst_wrapForalls] at Happ
      simpa [VExpr.instForallDomains_liftClosedDomains_succ] using Happ
    rcases ih Happ' with ⟨finalType, Htail⟩
    have Htail' : VEnv.TypedApplicationSpine env uvars ctx (.app fn arg)
        ((VExpr.wrapForalls (VExpr.liftClosedDomains types 1)
          resultType).inst arg) args finalType := by
      rw [VExpr.inst_wrapForalls,
        VExpr.instForallDomains_liftClosedDomains_succ]
      simpa using Htail
    refine ⟨finalType, ?_⟩
    simpa [VExpr.liftClosedDomains, VExpr.wrapForalls] using
      (VEnv.TypedApplicationSpine.cons Hfn' Harg Htail')

/-- If `left` and `right` have types with the same telescope domains for `args`
(`SameTelescopeDomains`) and `right` applied to `args` is well formed, then `left` applied to
`args` has the residual type obtained by instantiating the left forall telescope
(`VExpr.applyForallType`).  Each argument's typing is recovered from the right
application. -/
theorem VEnv.HasType.mkApps_sameTelescopeDomains_exact
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hdomains : SameTelescopeDomains args.length leftType rightType)
    (Hleft : env.HasType uvars ctx left leftType)
    (Hright : env.HasType uvars ctx right rightType)
    (HrightApps : VExpr.WF env uvars ctx (VExpr.mkApps right args)) :
    env.HasType uvars ctx (VExpr.mkApps left args)
      (VExpr.applyForallType leftType args) := by
  induction args generalizing left right leftType rightType with
  | nil =>
    cases Hdomains with
    | zero => simpa [VExpr.mkApps, VExpr.applyForallType] using Hleft
  | cons arg args ih =>
    cases Hdomains with
    | @succ domain leftBody rightBody arity Htail =>
      have Harg := VEnv.HasType.mkApps_head henv hctx Hright HrightApps
      have HleftApp := Hleft.app Harg
      have HrightApp := Hright.app Harg
      have Htail' := Htail.instN arg 0
      have HrightRest : VExpr.WF env uvars ctx
          (VExpr.mkApps (.app right arg) args) := by
        simpa [VExpr.mkApps] using HrightApps
      simpa [VExpr.mkApps, VExpr.applyForallType] using
        ih Htail' HleftApp HrightApp HrightRest

/-- Apply a family and a parallel motive to the same argument spine, then
apply the resulting motive to a major premise of the family application.
Typing of the shared arguments is recovered from the independently typed
family application and transported to the declared telescope by uniqueness.
The exact result sort is retained for consumers that must type an equation
body rather than merely prove that it is a type. -/
theorem RecursorMotiveTelescope.applyMajorTyped
    {args : List VExpr} {env : VEnv} {uvars : Nat} {ctx : List VExpr}
    {motive major : VExpr}
    (H : RecursorMotiveTelescope resultLevel args.length family
      familyType motiveType)
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType uvars))
    (Hfamily : env.HasType uvars ctx family familyType)
    (Hmotive : env.HasType uvars ctx motive motiveType)
    (Hmajor : env.HasType uvars ctx major (VExpr.mkApps family args)) :
    env.HasType uvars ctx
      (.app (VExpr.mkApps motive args) major) (.sort resultLevel) := by
  induction args generalizing family familyType motive motiveType with
  | nil =>
      cases H with
      | zero =>
          simpa [VExpr.mkApps, VExpr.inst] using
            VEnv.HasType.app Hmotive Hmajor
  | cons arg args ih =>
      cases H with
      | @succ _ domain familyBody motiveBody _ Htail =>
        have HfamilyAppType := Hmajor.isType henv hctx
        have HfamilyAppWF : VExpr.WF env uvars ctx
            (VExpr.mkApps family (arg :: args)) := by
          rcases HfamilyAppType with ⟨level, Htype⟩
          exact ⟨.sort level, Htype⟩
        have Hprefix := VExpr.WF.mkApps_fn henv hctx
          (fn := .app family arg) (args := args) HfamilyAppWF
        rcases Hprefix.app_inv henv hctx with
          ⟨actualDomain, actualBody, HfamilyActual, HargActual⟩
        have HfunctionEq := Hfamily.uniqU henv hctx HfamilyActual
        have HdomainEq :=
          (VEnv.IsDefEqU.forallE_inv henv hctx HfunctionEq).1
        rcases HdomainEq with ⟨domainLevel, HdomainEq⟩
        have Harg : env.HasType uvars ctx arg domain :=
          HdomainEq.defeq' HargActual
        have Hfamily' : env.HasType uvars ctx (.app family arg)
            (familyBody.inst arg) := Hfamily.app Harg
        have Hmotive' : env.HasType uvars ctx (.app motive arg)
            (motiveBody.inst arg) := Hmotive.app Harg
        have Htail' := Htail.instN arg 0
        have Htail'' : RecursorMotiveTelescope resultLevel args.length
            (.app family arg) (familyBody.inst arg)
            (motiveBody.inst arg) := by
          simpa [VExpr.inst, VExpr.inst_liftN_bvar, VExpr.inst_liftN] using Htail'
        exact ih Htail'' Hfamily' Hmotive' Hmajor

end VerifyInductive
end Lean4Lean
