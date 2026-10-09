import Lean4Lean.Verify.Inductive.Rules.RuleSyntax
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldTypeScope
import Lean4Lean.Verify.Inductive.Recursor.Binders.InductionHypothesisUniverses

/-! Typing of the minor pass of `mkRecInfos` (`loopUTemplates`, `loopCtors`,
`loopInd2`): every induction hypothesis, recursive-call template and minor premise
the executable declares is translated and well typed in the recursor context, and
the recorded rule templates are typed (`TypedRuleTemplates`). Part of the recursor
phase (section 3.2 of the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The alpha-invariant shape of a recursive-call template.  This is the
common normal form of the minor-pass `loopUArgs` run and the call generated
during rule construction. -/
def recCallTemplateShape
    (call : AddInductive.RecCallTemplate) (motives : Array Expr)
    (fieldBinders : List FVarId) : InductionHypothesisShape where
  ownerIdx := call.targetTypeIdx
  localArity := call.args.size
  localTelescope :=
    (call.lctx.mkForall call.args (.sort .zero)).abstractList fieldBinders
  motive :=
    (motives[call.targetTypeIdx]!.abstractList
      (ExprArrayFVarIds call.args)).abstractList fieldBinders call.args.size
  indices := call.targetIndices.map fun index =>
    (index.abstractList (ExprArrayFVarIds call.args)).abstractList
      fieldBinders call.args.size

/-- Typing of one recursive-call template produced by the minor pass.  The
minor pass does not yet know the complete mutual minor array, so this
structure is polymorphic in that array and in the
generated recursor levels.  Instantiation is nevertheless exact: its value is
the executable `RecCallTemplate.build`, not a separately rebuilt call. -/
structure TypedCallTemplate
    (stats : AddInductive.InductiveStats)
    (motives : Array Expr)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams) (rootScope : FVarId → Prop)
    (decl : VInductDecl) (depth : Nat) (field : Expr)
    (call : AddInductive.RecCallTemplate) : Prop where
  owner_lt : call.targetTypeIdx < motives.size
  semantic : ∀ (indTypes : Array InductiveType) (minors : Array Expr)
      (lvls : List Level),
    ∃ S : TypedRecursiveCall indTypes stats
        motives minors lvls R decl depth field
        (call.instantiate indTypes stats motives minors lvls),
      S.rootScope = rootScope ∧
        Nonempty S.MotiveApplication ∧
        ∀ fieldBinders,
          S.generated.replayTrace fieldBinders =
            recCallTemplateShape call motives fieldBinders
  /-- The argument telescope and exposed indices mention only the
  declaration's universe parameters. -/
  universes : (call.lctx.mkForall call.args (.sort .zero)).levelParamsIn root.lparams = true ∧
    ∀ e ∈ call.targetIndices.toList, e.levelParamsIn root.lparams = true

/-- Array alignment for the typed call templates (`TypedCallTemplate`) produced by
`loopUTemplates`.  Entry `j` is rooted after exactly the `j` earlier
hypotheses declared by that same loop, hence its validation depth is
`depth + j`. -/
structure TypedCallTemplates
    {recLparams : List Name}
    (Rroot : RecursorContextWF fieldRoot recLparams)
    (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (rootScope : FVarId → Prop)
    (fields hypotheses : Array Expr)
    (calls : Array AddInductive.RecCallTemplate) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ originRoot,
      ∃ Rorigin : RecursorContextWF originRoot recLparams,
        ∃ priorHypotheses : Array Expr,
          ∃ _ : RecursorFVarSuffix Rroot Rorigin priorHypotheses,
            priorHypotheses.size = j ∧ Rorigin.chk = Rroot.chk ∧
              Nonempty (TypedCallTemplate stats motives
                Rorigin rootScope decl (depth + j) fields[j]! calls[j]!)

theorem TypedCallTemplates.empty
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (rootScope : FVarId → Prop)
    (fields : Array Expr) :
    TypedCallTemplates R decl depth stats motives rootScope
      fields #[] #[] where
  size_eq := rfl
  entry j hj := by simp at hj

theorem TypedCallTemplates.pushCurrent
    {recLparams : List Name}
    {Rroot : RecursorContextWF fieldRoot recLparams}
    {R : RecursorContextWF c recLparams}
    {calls : Array AddInductive.RecCallTemplate}
    (Hsem : TypedCallTemplates Rroot decl depth stats
      motives rootScope fields hypotheses calls)
    (Hrecent : RecursorFVarSuffix Rroot R hypotheses)
    (hchk : R.chk = Rroot.chk)
    (call : AddInductive.RecCallTemplate)
    (S : TypedCallTemplate stats motives R rootScope decl
      (depth + hypotheses.size) fields[hypotheses.size]! call) :
    TypedCallTemplates Rroot decl depth stats motives rootScope
      fields (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) (calls.push call) := by
  refine {
    size_eq := by simpa using congrArg Nat.succ Hsem.size_eq
    entry := ?_ }
  intro j hj
  by_cases hlast : j = hypotheses.size
  · subst j
    have hcall : (calls.push call)[hypotheses.size]! = call := by
      rw [show hypotheses.size = calls.size from Hsem.size_eq.symm]
      simp
    rw [hcall]
    exact ⟨c, R, hypotheses, Hrecent, rfl, hchk, ⟨S⟩⟩
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases Hsem.entry j hjOld with
      ⟨originRoot, Rorigin, priorHypotheses, Hprior, hpriorSize, hchkO, S⟩
    have hjCalls : j < calls.size := by rw [Hsem.size_eq]; exact hjOld
    have hcall : (calls.push call)[j]! = calls[j]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos (by simp; omega), dif_pos hjCalls]
      exact Array.getElem_push_lt hjCalls
    rw [hcall]
    exact ⟨originRoot, Rorigin, priorHypotheses, Hprior,
      hpriorSize, hchkO, S⟩

/-- Sharpening a field up-set to a binder-order prefix of the fields.  The
fields form the newest-first prefix of the context, each
depends only on earlier binders, and no field lies in the root scope `P`. -/
theorem IsFVarUpSet.sharpenPrefix {P : FVarId → Prop} :
    ∀ (Δpre Δroot : VLCtx) (L : List FVarId),
      VLCtx.FVWF (Δpre ++ Δroot) →
      VLCtx.fvars Δpre = L.reverse →
      (∀ fv ∈ L, ¬ P fv) →
      IsFVarUpSet (fun fv => fv ∈ L ∨ P fv) (Δpre ++ Δroot) →
      ∀ k, IsFVarUpSet (fun fv => fv ∈ L.take k ∨ P fv) (Δpre ++ Δroot)
  | [], Δroot, L, _, hL, _, hup, k => by
    have hnil : L = [] := by simpa using hL.symm
    subst hnil
    simpa using hup
  | (none, d) :: Δpre, Δroot, L, hwf, hL, hfresh, hup, k =>
    sharpenPrefix Δpre Δroot L hwf.1 hL hfresh hup k
  | (some (fv, deps), d) :: Δpre, Δroot, L, hwf, hL, hfresh, hup, k => by
    have hcons : VLCtx.fvars ((some (fv, deps), d) :: Δpre) =
        fv :: VLCtx.fvars Δpre := by
      simp [VLCtx.fvars]
    rw [hcons] at hL
    obtain ⟨L', hL'⟩ : ∃ L', VLCtx.fvars Δpre = L'.reverse :=
      ⟨(VLCtx.fvars Δpre).reverse, by simp⟩
    have hLeq : L = L' ++ [fv] := by
      rw [hL'] at hL
      have := congrArg List.reverse hL
      simpa using this.symm
    subst hLeq
    have hfvTail : fv ∉ VLCtx.fvars (Δpre ++ Δroot) := (hwf.2 fv deps rfl).1
    have hdeps : deps ⊆ VLCtx.fvars (Δpre ++ Δroot) := (hwf.2 fv deps rfl).2
    have hfvL' : fv ∉ L' := by
      intro h
      apply hfvTail
      rw [VLCtx.fvars_append, hL']
      simp [h]
    have hcongrTail : ∀ Q₁ Q₂ : FVarId → Prop,
        (∀ x ∈ VLCtx.fvars (Δpre ++ Δroot), Q₁ x ↔ Q₂ x) →
        IsFVarUpSet Q₁ (Δpre ++ Δroot) → IsFVarUpSet Q₂ (Δpre ++ Δroot) :=
      fun _ _ h H => (IsFVarUpSet.congr hwf.1 h).mp H
    have hupTail : IsFVarUpSet (fun x => x ∈ L' ∨ P x) (Δpre ++ Δroot) := by
      refine hcongrTail _ _ ?_ hup.1
      intro x hx
      have hxfv : x ≠ fv := fun h => hfvTail (h ▸ hx)
      simp [hxfv]
    have ih := sharpenPrefix Δpre Δroot L' hwf.1 hL'
      (fun x hx => hfresh x (List.mem_append_left _ hx)) hupTail
    refine ⟨?_, ?_⟩
    · by_cases hk : k ≤ L'.length
      · have htake : (L' ++ [fv]).take k = L'.take k := by
          rw [List.take_append_of_le_length hk]
        rw [htake]
        exact ih k
      · have htake : (L' ++ [fv]).take k = L' ++ [fv] := by
          apply List.take_of_length_le
          simp
          omega
        rw [htake]
        exact hup.1
    · intro hfvScope x hx
      have hfvFull : fv ∈ L' ++ [fv] ∨ P fv := Or.inl (by simp)
      rcases hup.2 hfvFull x hx with hxL | hxP
      · left
        have hxTail : x ∈ VLCtx.fvars (Δpre ++ Δroot) := hdeps hx
        have hxfv : x ≠ fv := fun h => hfvTail (h ▸ hxTail)
        have hxL' : x ∈ L' := by
          rcases List.mem_append.mp hxL with h | h
          · exact h
          · simp at h
            exact absurd h hxfv
        rcases hfvScope with hfvTake | hfvP
        · have hk : L'.length < k := by
            by_contra hle
            have hle' : k ≤ L'.length := Nat.le_of_not_lt hle
            rw [List.take_append_of_le_length hle'] at hfvTake
            exact hfvL' (List.mem_of_mem_take hfvTake)
          rw [List.take_of_length_le (by simp; omega)]
          exact List.mem_append_left _ hxL'
        · exact absurd hfvP (hfresh fv (by simp))
      · exact Or.inr hxP

/-- Per-field variant of `TypedCallTemplates`: entry `j`
is scoped by `fieldScope j`, the up-set established for the `j`-th
selected recursive field.  Both rows come from the same
executable run; the coarse row serves the equation layer while this one
supports strengthening the call context to the field's own prefix. -/
structure TypedCallTemplatesAt
    {recLparams : List Name}
    (Rroot : RecursorContextWF fieldRoot recLparams)
    (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (fieldScope : Nat → FVarId → Prop)
    (fields hypotheses : Array Expr)
    (calls : Array AddInductive.RecCallTemplate) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ originRoot,
      ∃ Rorigin : RecursorContextWF originRoot recLparams,
        ∃ priorHypotheses : Array Expr,
          ∃ _ : RecursorFVarSuffix Rroot Rorigin priorHypotheses,
            priorHypotheses.size = j ∧ Rorigin.chk = Rroot.chk ∧
              Nonempty (TypedCallTemplate stats motives
                Rorigin (fieldScope j) decl (depth + j) fields[j]! calls[j]!)

theorem TypedCallTemplatesAt.empty
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (fieldScope : Nat → FVarId → Prop)
    (fields : Array Expr) :
    TypedCallTemplatesAt R decl depth stats motives fieldScope
      fields #[] #[] where
  size_eq := rfl
  entry j hj := by simp at hj

theorem TypedCallTemplatesAt.pushCurrent
    {recLparams : List Name}
    {Rroot : RecursorContextWF fieldRoot recLparams}
    {R : RecursorContextWF c recLparams}
    {calls : Array AddInductive.RecCallTemplate}
    (Hsem : TypedCallTemplatesAt Rroot decl depth stats
      motives fieldScope fields hypotheses calls)
    (Hrecent : RecursorFVarSuffix Rroot R hypotheses)
    (hchk : R.chk = Rroot.chk)
    (call : AddInductive.RecCallTemplate)
    (S : TypedCallTemplate stats motives R
      (fieldScope hypotheses.size) decl
      (depth + hypotheses.size) fields[hypotheses.size]! call) :
    TypedCallTemplatesAt Rroot decl depth stats motives
      fieldScope fields (hypotheses.push (.fvar ⟨c.ngen.curr⟩))
      (calls.push call) := by
  refine {
    size_eq := by simpa using congrArg Nat.succ Hsem.size_eq
    entry := ?_ }
  intro j hj
  by_cases hlast : j = hypotheses.size
  · subst j
    have hcall : (calls.push call)[hypotheses.size]! = call := by
      rw [show hypotheses.size = calls.size from Hsem.size_eq.symm]
      simp
    rw [hcall]
    exact ⟨c, R, hypotheses, Hrecent, rfl, hchk, ⟨S⟩⟩
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases Hsem.entry j hjOld with
      ⟨originRoot, Rorigin, priorHypotheses, Hprior, hpriorSize, hchkO, S⟩
    have hjCalls : j < calls.size := by rw [Hsem.size_eq]; exact hjOld
    have hcall : (calls.push call)[j]! = calls[j]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos (by simp; omega), dif_pos hjCalls]
      exact Array.getElem_push_lt hjCalls
    rw [hcall]
    exact ⟨originRoot, Rorigin, priorHypotheses, Hprior,
      hpriorSize, hchkO, S⟩

/-- The scope of one selected recursive field: the parameters together
with the constructor fields before that field, in binder order.  The
field's declared type and the domains of its induction hypothesis can
therefore be strengthened to the field's own prefix context. -/
def RecursorFieldPrefixScope (params : Array Expr) (fields : List FVarId)
    (field : Expr) (fv : FVarId) : Prop :=
  fv ∈ fields.take (fields.idxOf (recursorFVarId field)) ∨
    fv ∈ ExprArrayFVarIds params

/-- Typing of a constructor field traversal, at the contexts where the
traversal ran. -/
structure TypedRuleFieldTraversal
    {recLparams : List Name}
    (Rambient : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (S : MinorPremiseType) where
  traversal : ConstructorFieldTraversal
  traversal_eq : S.traversal = some traversal
  traversal_constructor : traversal.constructor = S.constructor
  traversal_fields : traversal.fields = S.fields
  traversal_recursiveFields : traversal.recursiveFields = S.recursiveFields
  traversal_stats : traversal.stats = stats
  rootWF : RecursorContextWF traversal.rootContext recLparams
  terminalWF : RecursorContextWF traversal.terminalContext recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix rootWF stats parameterDepth
  terminalExtension : RecursorContextExtension terminalWF Rambient
  fieldsRecent : RecursorFVarSuffix rootWF terminalWF S.fields
  parameterTarget : VExpr
  parameterTail_params : traversal.parameterTail.FVarsIn
    (· ∈ ExprArrayFVarIds stats.params)
  parameterTranslation : TrExprS rootWF.venv recLparams rootWF.mlctx.vlctx
    traversal.parameterTail parameterTarget
  parameterType : rootWF.venv.IsType recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
  /-- The constructor tail, translated in the parameter declarations alone. -/
  parameterTranslation₀ : ∃ t, TrExprS rootWF.venv recLparams
      parameterSuffix.parameterDecls traversal.parameterTail t ∧
    rootWF.venv.IsType recLparams.length
      parameterSuffix.parameterDecls.toCtx t
  fieldOpening : ConstructorFieldOpening traversal.parameterTail
    traversal.terminal S.fields
  fieldParameterUp : IsFVarUpSet (fun fv => fv ∈ fieldsRecent.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params) terminalWF.mlctx.vlctx
  fieldCheck : ∃ M : TypeChecker.MLCtx, M.WF terminalWF.venv recLparams ∧
    (0 < S.fields.size → terminalWF.chk = M) ∧
    ∃ hn : S.fields.size ≤ M.length,
      MLCtxTopAgree terminalWF.mlctx M S.fields.size ∧
        (M.dropN S.fields.size hn).vlctx = parameterSuffix.parameterDecls ∧
        ∃ T₀, TrExprS rootWF.venv recLparams parameterSuffix.parameterDecls
          traversal.parameterTail T₀ ∧
        ∃ t₀', TrExprS terminalWF.venv recLparams M.vlctx
          traversal.terminal t₀' ∧
          terminalWF.venv.IsDefEqU recLparams.length
            parameterSuffix.parameterDecls.toCtx T₀
            (M.mkForall' S.fields.size hn t₀')
  terminalTarget : VExpr
  terminalTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx traversal.terminal terminalTarget
  terminalType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx terminalTarget
  constructorApplication : ConstructorApplicationAt terminalWF stats
    traversal.constructor traversal.terminal S.fields terminalTarget
  fieldTargetDefEq : rootWF.venv.IsDefEqU recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
      (terminalWF.mlctx.mkForall' S.fields.size fieldsRecent.size_le
        terminalTarget)

def TypedRuleFieldTraversal.mono
    (F : TypedRuleFieldTraversal R stats S)
    (E : RecursorContextExtension R R') :
    TypedRuleFieldTraversal R' stats S :=
  { F with terminalExtension := F.terminalExtension.trans E }

/-- Lookup of the motive binder and its generated telescope, rooted at the
context of the minor pass, for every member of a mutual block.  It is built
from the motive pass's bindings, binder types, shapes, and telescopes; users supply
only the later context and the inductive application already validated by the
checker. -/
structure MotiveTelescopesAt
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  /-- The motive binding already exists at the root.  Recording it
  spares later equation proofs from constructing a false extension
  between sibling constructor contexts merely to recover binder freshness. -/
  rootBinding : ∀ target (_htarget : target < recInfos.size),
    Nonempty (MotiveBinding Rroot recInfos[target]! elimLevel)
  appliesTo : ∀ target (_htarget : target < recInfos.size)
      {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      (_Hext : RecursorContextExtension Rroot Rcurrent)
      {depth : Nat} {exposedType : Expr} {syntaxTarget : VExpr},
    TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
    Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx
        syntaxTarget →
    RecursorValidatedIndAppAt Rcurrent.venv recLparams
        Rcurrent.mlctx.vlctx stats decl depth exposedType syntaxTarget target →
    ∃ binding : MotiveBinding Rcurrent recInfos[target]! elimLevel,
      Nonempty (MotiveAppliesTo Rcurrent stats
        recInfos[target]! binding exposedType syntaxTarget)

theorem MotiveTelescopesAt.of
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (T : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoBinderTypes root recInfos)
    (Hshapes : MotiveTypes root recInfos Horigins.motiveTypes
      elimLevel) :
    MotiveTelescopesAt Rroot stats decl recInfos elimLevel where
  rootBinding target htarget := by
    exact Hshapes.motiveBindingMono Hbindings Horigins
        (RecursorContextExtension.refl Rroot).contextLE target htarget
  appliesTo target htarget _current Rcurrent Hext _depth _exposedType
      _syntaxTarget Hexposed HsyntaxType Hvalidated := by
    rcases Hshapes.motiveBindingMono (Rcurrent := Rcurrent)
        Hbindings Horigins Hext.contextLE target htarget with ⟨binding⟩
    exact ⟨binding, T.telescope target htarget Rcurrent Hext binding
      Hexposed HsyntaxType Hvalidated⟩

/-- Typing of one rule-template row.  It is indexed by
the minor shape and template, so later installation cannot
pair a typed call row with an unrelated executable rule. -/
def TypedRuleTemplateAt
    {recLparams : List Name}
    (Rambient : RecursorContextWF c recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (elimLevel : Level) (parameterDecls : VLCtx)
    (expectedOwnerIdx : Nat) (S : MinorPremiseType)
    (B : AddInductive.RecRuleTemplate) : Prop :=
  ∃ origins : MinorInductionHypothesisTypes S.sourceFullContext
      S.recursiveFields S.hypotheses,
    S.hypothesis_type_origins = some origins ∧
    origins.stats = stats ∧
    origins.recInfos.map (·.motive) = recInfos.map (·.motive) ∧
    ∃ F : TypedRuleFieldTraversal Rambient stats S,
      F.parameterSuffix.parameterDecls = parameterDecls ∧
      ∃ depth,
        RecursorValidAppStatsWF F.terminalWF.venv recLparams
          F.terminalWF.mlctx.vlctx stats decl depth ∧
        ∃ fields : List (RecursiveFieldDomainAt F.terminalWF.venv decl
            recLparams.length),
          RecursiveFieldSelectionsAt F.terminalWF.venv decl recLparams.length
            S.fields S.recursiveFields fields ∧
          AddInductive.isValidIndAppIdx stats F.traversal.terminal
            expectedOwnerIdx = true ∧
          expectedOwnerIdx < decl.types.length ∧
          ∃ ownerIdx,
            AddInductive.isValidIndApp? stats F.traversal.terminal =
              some ownerIdx ∧
            Nonempty (RecursorValidatedIndAppAt F.terminalWF.venv recLparams
              F.terminalWF.mlctx.vlctx stats decl depth F.traversal.terminal
              F.terminalTarget ownerIdx) ∧
        ∃ binding : MotiveBinding F.terminalWF
            recInfos[ownerIdx]! elimLevel,
          Nonempty (MotiveAppliesTo F.terminalWF stats
            recInfos[ownerIdx]! binding F.traversal.terminal
            F.terminalTarget) ∧
        Nonempty (MotiveTelescopesAt F.terminalWF stats decl recInfos
          elimLevel) ∧
        Nonempty (TypedCallTemplates F.terminalWF decl depth
          stats (recInfos.map (·.motive))
          (fun fv => fv ∈ F.fieldsRecent.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params)
          S.recursiveFields S.hypotheses B.recursiveCalls) ∧
        Nonempty (TypedCallTemplatesAt F.terminalWF decl
          depth stats (recInfos.map (·.motive))
          (fun j => RecursorFieldPrefixScope stats.params F.fieldsRecent.fvars
            S.recursiveFields[j]!)
          S.recursiveFields S.hypotheses B.recursiveCalls)

theorem TypedRuleTemplateAt.mono
    {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {R' : RecursorContextWF c' recLparams}
    (H : TypedRuleTemplateAt R decl stats recInfos elimLevel
      parameterDecls
      expectedOwnerIdx S B)
    (E : RecursorContextExtension R R') :
    TypedRuleTemplateAt R' decl stats recInfos elimLevel
      parameterDecls
      expectedOwnerIdx S B := by
  unfold TypedRuleTemplateAt at H ⊢
  rcases H with
    ⟨origins, hshape, hstats, hmotives, F, hparams, depth, HvalidStats,
      fields, Hselection, hexpectedValid, hexpectedLt,
      ownerIdx, htargetValid, Hvalidated, binding, Hevidence,
      Hlookup, Hcalls, Hsharp⟩
  exact ⟨origins, hshape, hstats, hmotives, F.mono E, hparams, depth,
    HvalidStats, fields, Hselection, hexpectedValid, hexpectedLt,
    ownerIdx, htargetValid, Hvalidated, binding, Hevidence, Hlookup, Hcalls,
    Hsharp⟩

/-- Owner/minor-indexed typed rule-template rows (`TypedRuleTemplateAt`),
maintained through the minor pass. -/
structure TypedRuleTemplates
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (elimLevel : Level) (parameterDecls : VLCtx)
    (Horigins : RecInfoBinderTypes c recInfos) : Prop where
  rows_size : ∀ owner (_howner : owner < recInfos.size),
    recInfos[owner]!.ruleTemplates.size =
      Horigins.minorTypes[owner]!.size
  entry : ∀ owner (howner : owner < recInfos.size)
      (localIndex : Nat)
      (hlocal : localIndex < Horigins.minorTypes[owner]!.size),
    Nonempty (TypedRuleTemplateAt R decl stats recInfos elimLevel
      parameterDecls
      owner
      (Horigins.minorShapes owner howner localIndex hlocal)
      recInfos[owner]!.ruleTemplates[localIndex]!)
  /-- Every field binder is distinct from every binder in the
  recursor prefix.  Later minor
  allocations preserve earlier rows because their fresh id is not in the
  current context, while a new row was opened after the prefix
  that already existed. -/
  fields_outer_fresh : ∀ owner (howner : owner < recInfos.size)
      (localIndex : Nat)
      (hlocal : localIndex < Horigins.minorTypes[owner]!.size)
      (fv : FVarId),
    fv ∈ (Horigins.minorShapes owner howner localIndex hlocal).fields_bound.fvars →
    fv ∉ (ExprArrayFVarIds stats.params ++
      ExprArrayFVarIds (recInfos.map (·.motive))) ++
      ExprArrayFVarIds (recInfos.flatMap (·.minors))

theorem TypedRuleTemplates.mono
    {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {R' : RecursorContextWF c' recLparams}
    (H : TypedRuleTemplates R decl stats recInfos elimLevel
      parameterDecls Horigins)
    (E : RecursorContextExtension R R') :
    TypedRuleTemplates R' decl stats recInfos elimLevel
      parameterDecls
      (Horigins.mono E.contextLE) := by
  refine {
    rows_size := H.rows_size
    entry := ?_
    fields_outer_fresh := ?_ }
  · intro owner howner localIndex hlocal
    have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
      simpa [RecInfoBinderTypes.mono] using hlocal
    rcases H.entry owner howner localIndex hlocalOld with ⟨Hentry⟩
    exact ⟨by simpa [RecInfoBinderTypes.mono] using Hentry.mono E⟩
  · intro owner howner localIndex hlocal fv hfv
    simpa [RecInfoBinderTypes.mono] using
      H.fields_outer_fresh owner howner localIndex hlocal fv hfv

/-- Before the minor pass begins, every minor/template row is
empty, so `TypedRuleTemplates` holds without any entries. -/
theorem TypedRuleTemplates.ofEmpty
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hcounts : RecInfoTemplateCounts recInfos) (elimLevel : Level) :
    TypedRuleTemplates R decl stats recInfos elimLevel
      parameterDecls Horigins where
  rows_size owner howner :=
    (Hcounts owner howner).trans
      (Horigins.minors owner howner).size_eq.symm
  entry owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega
  fields_outer_fresh owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega

namespace mkRecInfos.loopCtorArgs.loop

end mkRecInfos.loopCtorArgs.loop

namespace mkRecInfos.loopUTemplates

/-- Typing of the hypothesis loop `loopUTemplates`.  The
proof follows the executable run; the continuation receives both the
fresh hypotheses and the call-template row of the same size. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (bu u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallTemplate →
      AddInductive.M alpha)
    {recLparams : List Name}
    {root current : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF current recLparams)
    (rootScope : FVarId → Prop)
    (rootScopeInContext : ∀ fv, rootScope fv → fv ∈ Rroot.mlctx.vlctx.fvars)
    (hrootUp : IsFVarUpSet rootScope Rroot.mlctx.vlctx)
    (i : Nat) (v : Array Expr)
    (calls : Array AddInductive.RecCallTemplate)
    (Hrecent : RecursorFVarSuffix Rroot R v)
    (Horigins : InductionHypothesisTypesPrefix stats recInfos root current u v)
    (HcallOrigins : CallTemplatesMatchPrefix Horigins rootScope
      calls)
    (HcallSemantics : TypedCallTemplates Rroot decl depth
      stats (recInfos.map (·.motive)) rootScope u v calls)
    (fieldScope : Nat → FVarId → Prop)
    (HsharpSemantics : TypedCallTemplatesAt Rroot decl depth
      stats (recInfos.map (·.motive)) fieldScope u v calls)
    (hprocessed : v.size = i)
    (hcalls : calls.size = v.size)
    (hcheck : current.checkLCtx = root.checkLCtx)
    (hchkR : R.chk = Rroot.chk)
    (Hvi : ∀ {next : AddInductive.Context}
      (Rnext : RecursorContextWF next recLparams)
      {prior : Array Expr}
      (_Hprior : RecursorFVarSuffix Rroot Rnext prior)
      (_hcheckNext : next.checkLCtx = root.checkLCtx)
      (j : Nat) (hj : j < u.size),
      ((AddInductive.mkRecInfos.loopUArgs
          (AddInductive.mkRecInfos.fieldsBefore stats bu u[j]) u[j] fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let lctx ← getLCtx
        let motiveApp := .app
          (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[j] xs)
        let viTy := lctx.mkForall xs motiveApp
        return (viTy, ({
          major := u[j]
          args := xs
          lctx := lctx
          targetTypeIdx := itIdx
          targetIndices := itIndices
          template := lctx.mkLambda xs <|
            (mkAppN (.bvar xs.size) itIndices).app (mkAppN u[j] xs) } :
            AddInductive.RecCallTemplate))) next).WF fun result =>
          ∃ viTarget,
            TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
              (result.1.consumeTypeAnnotationsVerified next.env.isTypeAnnotationWrapper) viTarget ∧
            Rnext.venv.IsType recLparams.length
              Rnext.mlctx.vlctx.toCtx viTarget ∧
            ∃ O : InductionHypothesisTypeAt
                stats recInfos next u[j]! result.1,
              result.2 = {
                major := u[j]!
                args := O.args
                lctx := O.current.lctx
                targetTypeIdx := O.ownerIdx
                targetIndices :=
                  O.exposedType.getAppArgs[stats.params.size:]
                template := O.current.lctx.mkLambda O.args <|
                  (mkAppN (.bvar O.args.size)
                    O.exposedType.getAppArgs[stats.params.size:]).app
                      (mkAppN u[j]! O.args) } ∧
              TypedCallTemplate stats
                (recInfos.map (·.motive)) Rnext rootScope decl
                (depth + prior.size) u[j]! result.2 ∧
              TypedCallTemplate stats
                (recInfos.map (·.motive)) Rnext (fieldScope j) decl
                (depth + prior.size) u[j]! result.2)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (outCalls : Array AddInductive.RecCallTemplate),
      RecursorFVarSuffix Rroot Rout values →
      (HoutOrigins : InductionHypothesisTypesPrefix
        stats recInfos root out u values) →
      CallTemplatesMatchPrefix HoutOrigins rootScope outCalls →
      TypedCallTemplates Rroot decl depth stats
        (recInfos.map (·.motive)) rootScope u values outCalls →
      TypedCallTemplatesAt Rroot decl depth stats
        (recInfos.map (·.motive)) fieldScope u values outCalls →
      values.size = v.size + (u.size - i) →
      outCalls.size = values.size →
      (k values outCalls out).WF Q) :
    (AddInductive.mkRecInfos.loopUTemplates stats bu u recInfos i v calls
      k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopUTemplates]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    refine (Hvi R Hrecent hcheck i hnext).bind fun result Hresult => ?_
    rcases result with ⟨viTy, call⟩
    rcases Hresult with
      ⟨viTarget, HviTr, HviType, O, hcall, HcallSemantic, HsharpSemantic⟩
    subst i
    have hget : ((getLCtx : AddInductive.M LocalContext) current).WF
        (fun lctx => lctx = current.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName :=
      (current.lctx.get! u[v.size].fvarId!).userName.appendAfter "_ih"
    refine withLocalDecl.recursorWF (name := vName) (bi := .default)
      R HviTr HviType ?_
    let R' := R.withLocalDecl (name := vName) (bi := .default)
      HviTr HviType
    refine resultBindings stats bu u recInfos k Rroot R' rootScope
      rootScopeInContext hrootUp (v.size + 1)
      (v.push (.fvar ⟨current.ngen.curr⟩)) (calls.push call)
      (Hrecent.pushCurrent vName (viTy.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) viTarget
        .default HviTr HviType)
      (Horigins.pushCurrent R.toBindingContextWF vName viTy .default
        hnext Hrecent.contextLE ⟨O⟩)
      (HcallOrigins.pushCurrent R.toBindingContextWF vName viTy .default
        hnext Hrecent.contextLE R (Hrecent.upsetRoot rootScopeInContext hrootUp)
        O call hcall)
      (HcallSemantics.pushCurrent Hrecent hchkR call HcallSemantic)
      fieldScope
      (HsharpSemantics.pushCurrent Hrecent hchkR call HsharpSemantic)
      (by simp) (by simp [hcalls]) hcheck hchkR Hvi ?_
    intro out Rout values outCalls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics HvalueSharpSemantics hsize hcallSize
    apply Hk Rout values outCalls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics HvalueSharpSemantics
    · simp only [Array.size_push] at hsize
      omega
    · exact hcallSize
  · rw [dif_neg hnext]
    exact Hk R v calls Hrecent Horigins HcallOrigins HcallSemantics
      HsharpSemantics (by omega) hcalls
termination_by u.size - i

/-- Pointwise typing of the pair returned by the
template-producing `loopUArgs` callback. -/
theorem inductionHypothesisTypeOriginOfInferredScope
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    (prior : Array Expr)
    (hpriorFVars : ∃ k, prior.toList.map (·.fvarId!) =
        ((c.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
      ((c.checkLCtx.toList.map (·.fvarId)).reverse)[k]? =
        some (Expr.fvar fv).fvarId!)
    {rootScope : FVarId → Prop}
    (hinferredScope : (AddInductive.getType (.fvar fv) c).WF fun ty => ty.FVarsIn rootScope)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (hscopeUniverses : R.typeChecker.UniverseScope c.lparams rootScope ∧
      ∀ ty, (AddInductive.getType (.fvar fv) c) = .ok ty → ty.levelParamsIn c.lparams = true)
    (Hmotives : FVarArrayIn c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorFVarSuffix R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget) :
    (AddInductive.mkRecInfos.loopUArgs prior (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let targetIndices := exposedType.getAppArgs[stats.params.size:]
        let lctx ← getLCtx
        let motiveApp := Expr.app
          (mkAppN recInfos[target]!.motive targetIndices)
          (mkAppN (.fvar fv) args)
        let viTy := lctx.mkForall args motiveApp
        return (viTy, ({
          major := .fvar fv
          args := args
          lctx := lctx
          targetTypeIdx := target
          targetIndices := targetIndices
          template := lctx.mkLambda args <|
            (mkAppN (.bvar args.size) targetIndices).app
              (mkAppN (.fvar fv) args) } :
            AddInductive.RecCallTemplate))) c).WF fun result =>
        ∃ viTarget,
          TrExprS R.venv recLparams R.mlctx.vlctx
            (result.1.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) viTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
          ∃ O : InductionHypothesisTypeAt
              stats recInfos c (.fvar fv) result.1,
            result.2 = {
              major := .fvar fv
              args := O.args
              lctx := O.current.lctx
              targetTypeIdx := O.ownerIdx
              targetIndices :=
                O.exposedType.getAppArgs[stats.params.size:]
              template := O.current.lctx.mkLambda O.args <|
                (mkAppN (.bvar O.args.size)
                  O.exposedType.getAppArgs[stats.params.size:]).app
                    (mkAppN (.fvar fv) O.args) } ∧
            TypedCallTemplate stats
              (recInfos.map (·.motive)) R rootScope decl depth
              (.fvar fv) result.2 := by
  let build : Expr → Array Expr → Nat →
      AddInductive.M (Expr × AddInductive.RecCallTemplate) :=
    fun exposedType args target => do
      let targetIndices := exposedType.getAppArgs[stats.params.size:]
      let lctx ← getLCtx
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive targetIndices)
        (mkAppN (.fvar fv) args)
      let viTy := lctx.mkForall args motiveApp
      return (viTy, {
        major := .fvar fv
        args := args
        lctx := lctx
        targetTypeIdx := target
        targetIndices := targetIndices
        template := lctx.mkLambda args <|
          (mkAppN (.bvar args.size) targetIndices).app
            (mkAppN (.fvar fv) args) })
  have hfvScope : fv ∈ R.mlctx.vlctx.fvars := by
    simpa only [FVarsIn] using hfield.fvarsIn
  have hfvRoot : fv ∈ c.lctx.fvars := by
    rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq]
    exact hfvScope
  have Hrun := mkRecInfos.loopUArgs.resultRecursiveDomainOfInferredScope fv stats build
    c R Hstats hconsume hlit hctx hfield prior hpriorFVars hinferredScope hrootUp
    (Q := fun target result => ∃ viTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        (result.1.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) viTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
      ∃ O : InductionHypothesisTypeAt
          stats recInfos c (.fvar fv) result.1,
        O.ownerIdx = target ∧
        result.2 = {
          major := .fvar fv
          args := O.args
          lctx := O.current.lctx
          targetTypeIdx := O.ownerIdx
          targetIndices :=
            O.exposedType.getAppArgs[stats.params.size:]
          template := O.current.lctx.mkLambda O.args <|
            (mkAppN (.bvar O.args.size)
              O.exposedType.getAppArgs[stats.params.size:]).app
                (mkAppN (.fvar fv) O.args) } ∧
        ∀ (domain : VExpr),
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
            fieldTarget domain →
          ∀ (htarget : O.ownerIdx < decl.types.length),
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[O.ownerIdx]'htarget).name
              R.mlctx.vlctx.toCtx depth domain →
          TypedCallTemplate stats
            (recInfos.map (·.motive)) R rootScope decl depth
            (.fvar fv) result.2) ?_
  · change (AddInductive.mkRecInfos.loopUArgs prior (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        build exposedType args target) c).WF _
    exact Hrun.mono (fun result Hout => by
      rcases Hout with ⟨domain, hfieldType, target, htarget,
        hrecursive, viTarget, Hvi, HviType, O, howner, hcall, Hsemantic⟩
      subst target
      exact ⟨viTarget, Hvi, HviType, O, hcall,
        Hsemantic domain hfieldType htarget hrecursive⟩)
  · intro Hinput current Rcurrent exposedType syntaxTarget terminalTarget
      appliedTarget args target Htrace Hexposed Hdefeq Hterminal Hargs Happlied
      HappliedType hvalid hexposedScope hup hchkAgree
    rcases Happ Rcurrent Hexposed Hdefeq Hterminal Hargs Happlied
        HappliedType hvalid with ⟨motiveTarget, Hmotive, HmotiveType⟩
    have htargetStats : target < stats.indConsts.size :=
      (checkPositivityStep.isValidIndApp?_some hvalid).1
    have htarget : target < recInfos.size := by
      rw [hrecords]
      exact htargetStats
    rcases Hmotives.get_eq_fvar target
        (by simpa using htarget) with
      ⟨motiveFVar, hmotiveFVar, hmotiveMember⟩
    rcases Hargs.mkForall Hmotive HmotiveType with
      ⟨viTarget, Hvi, HviType⟩
    let targetIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive targetIndices)
      (mkAppN (.fvar fv) args)
    rcases hconsume c recLparams R Hvi HviType with
      ⟨consumedTarget, Hconsumed⟩
    change (Except.ok (current.lctx.mkForall args motiveApp,
      ({
        major := .fvar fv
        args := args
        lctx := current.lctx
        targetTypeIdx := target
        targetIndices := targetIndices
        template := current.lctx.mkLambda args <|
          (mkAppN (.bvar args.size) targetIndices).app
            (mkAppN (.fvar fv) args) } :
          AddInductive.RecCallTemplate))).WF _
    let O : InductionHypothesisTypeAt stats recInfos c
        (.fvar fv) (current.lctx.mkForall args motiveApp) := {
        current := current
        current_wf := Rcurrent.toBindingContextWF
        current_extends := Hargs.contextLE
        exposedType := exposedType
        args := args
        arguments_bound := Hargs.toFVarArrayAfter
        loopInput := Hinput
        loopTrace := Htrace
        field_fvar := ⟨fv, rfl, hfvRoot⟩
        ownerIdx := target
        owner_valid := hvalid
        motive_is_fvar := ⟨motiveFVar, by
          rw [getElem!_pos recInfos target htarget]
          simpa only [Array.getElem_map] using hmotiveFVar,
          hmotiveMember⟩
        type_eq := rfl }
    refine Except.WF.pure
      ⟨consumedTarget, Hconsumed.unannotated, Hconsumed.isType, O, rfl, rfl, ?_⟩
    intro domain hfieldTyping htargetDecl hrecursive
    have hcallUniverses := Hinput.callUniverses hconsume Htrace R hscopeUniverses.1
      hfield (hscopeUniverses.2 _ Hinput.inference)
      (hinferredScope _ Hinput.inference) Hargs.toFVarArrayAfter
      Rcurrent.toBindingContextWF stats.params.size
    refine {
      owner_lt := by simpa using htarget
      semantic := ?_
      universes := hcallUniverses }
    intro indTypes minors lvls
    let call : AddInductive.RecCallTemplate := {
      major := .fvar fv
      args := args
      lctx := current.lctx
      targetTypeIdx := target
      targetIndices := targetIndices
      template := current.lctx.mkLambda args <|
        (mkAppN (.bvar args.size) targetIndices).app
          (mkAppN (.fvar fv) args) }
    let value := call.instantiate indTypes stats (recInfos.map (·.motive))
      minors lvls
    let Hgenerated : RecursiveCall indTypes stats
        (recInfos.map (·.motive)) minors lvls c (.fvar fv) value := {
      exposedType := exposedType
      ownerIdx := target
      owner_valid := hvalid
      localArgs := args
      current := current
      current_wf := Rcurrent.toBindingContextWF
      current_extends := Hargs.contextLE
      arguments_bound := Hargs.toFVarArrayAfter
      value_eq := by
        simp [value, call, AddInductive.RecCallTemplate.instantiate,
          AddInductive.getIIndices, hvalid, targetIndices] }
    let HstatsCurrent := Hstats.weakenRecent Hargs
    have hctxCurrent : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
      Hargs.noIndConsts (names := decl.types.map (·.name)) hctx
    let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
      htargetDecl (by simpa only [Hargs.venv_eq] using hlit)
      hctxCurrent
    have HexposedType : Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget :=
      VEnv.IsType.defeqU_l Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm Hterminal
    have HappliedType' : Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget syntaxTarget :=
      HappliedType.defeqU_r Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
    let commonDomains := MLCtxForallDomains Rcurrent.mlctx
      args.size Hargs.size_le
    have HexposedClosed := Hargs.mkForallExact Hexposed HexposedType
    have HappliedClosed := Hargs.mkLambda Happlied HappliedType'
    let S : TypedRecursiveCall indTypes stats
        (recInfos.map (·.motive)) minors lvls R decl depth (.fvar fv)
        value := {
      generated := Hgenerated
      current_context := Rcurrent
      recent := Hargs
      rootScope := rootScope
      exposed_scope := hexposedScope
      current_scope_up := hup
      chkAgree := hchkAgree
      exposedTarget := syntaxTarget
      exposed_translation := Hexposed
      terminalTarget := terminalTarget
      exposed_defeq := Hdefeq
      terminal_type := Hterminal
      appliedFieldTarget := appliedTarget
      applied_field_translation := Happlied
      applied_field_typing := HappliedType
      validated := Hvalidated
      commonDomains := commonDomains
      commonDomains_length :=
        Rcurrent.onlyLams.forallDomains_length args.size Hargs.size_le
      common_exposed_translation := by
        simpa [commonDomains] using HexposedClosed.1
      common_exposed_type := by
        simpa [commonDomains] using HexposedClosed.2
      common_applied_translation := by
        simpa [commonDomains] using HappliedClosed.1
      common_applied_typing := by
        simpa [commonDomains] using HappliedClosed.2
      fieldTarget := fieldTarget
      domain := domain
      field_translation := hfield
      field_typing := hfieldTyping
      owner_lt := htargetDecl
      recursive := hrecursive }
    refine ⟨S, rfl, ?_, ?_⟩
    · refine ⟨{
        target := motiveTarget
        translation := ?_
        typing := HmotiveType }⟩
      simpa [S, Hgenerated, targetIndices, Array.getElem!_eq_getD,
        Array.getD, htarget] using Hmotive
    · intro fieldBinders
      simp [S, Hgenerated,
        RecursiveCall.replayTrace,
        recCallTemplateShape,
        Hargs.toFVarArrayAfter.toFVarArrayIn.exprArrayFVarIds]
      rfl

/-- Form of `inductionHypothesisTypeOriginOfInferredScope` in which the
field's own membership in the up-set scopes its inferred type through the
`FVarsBelow` contract. -/
theorem inductionHypothesisTypeOrigin
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    (prior : Array Expr)
    (hpriorFVars : ∃ k, prior.toList.map (·.fvarId!) =
        ((c.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
      ((c.checkLCtx.toList.map (·.fvarId)).reverse)[k]? =
        some (Expr.fvar fv).fvarId!)
    {rootScope : FVarId → Prop}
    (hfieldScope : rootScope fv)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (hrootUniverses : R.typeChecker.UniverseScope c.lparams rootScope)
    (Hmotives : FVarArrayIn c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorFVarSuffix R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget) :
    (AddInductive.mkRecInfos.loopUArgs prior (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let targetIndices := exposedType.getAppArgs[stats.params.size:]
        let lctx ← getLCtx
        let motiveApp := Expr.app
          (mkAppN recInfos[target]!.motive targetIndices)
          (mkAppN (.fvar fv) args)
        let viTy := lctx.mkForall args motiveApp
        return (viTy, ({
          major := .fvar fv
          args := args
          lctx := lctx
          targetTypeIdx := target
          targetIndices := targetIndices
          template := lctx.mkLambda args <|
            (mkAppN (.bvar args.size) targetIndices).app
              (mkAppN (.fvar fv) args) } :
            AddInductive.RecCallTemplate))) c).WF fun result =>
        ∃ viTarget,
          TrExprS R.venv recLparams R.mlctx.vlctx
            (result.1.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) viTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
          ∃ O : InductionHypothesisTypeAt
              stats recInfos c (.fvar fv) result.1,
            result.2 = {
              major := .fvar fv
              args := O.args
              lctx := O.current.lctx
              targetTypeIdx := O.ownerIdx
              targetIndices :=
                O.exposedType.getAppArgs[stats.params.size:]
              template := O.current.lctx.mkLambda O.args <|
                (mkAppN (.bvar O.args.size)
                  O.exposedType.getAppArgs[stats.params.size:]).app
                    (mkAppN (.fvar fv) O.args) } ∧
            TypedCallTemplate stats
              (recInfos.map (·.motive)) R rootScope decl depth
              (.fvar fv) result.2 :=
  inductionHypothesisTypeOriginOfInferredScope fv stats recInfos c R Hstats hconsume hlit
    hctx hfield prior hpriorFVars
    ((getTypeFVarInRecursorContext.WF R hfield).mono fun _ ⟨_, hbelow, _, _, _⟩ =>
      hbelow rootScope hrootUp (by simpa only [FVarsIn] using hfieldScope))
    hrootUp
    ⟨hrootUniverses, fun ty hty =>
      getTypeFVarInRecursorContext.levelsWF R hfield ty hty c.lparams rootScope
        hrootUniverses rfl (by simpa only [FVarsIn] using hfieldScope)⟩
    Hmotives hrecords Happ

/-- Close the template-producing hypothesis loop from the
verified motive applications.  The additional output is produced by the same
successful traversal, so no premise comparing two runs up to alpha is needed. -/
theorem resultTypingOfMotiveApplications
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (bu u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallTemplate →
      AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (rootScope : FVarId → Prop)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget ∧ rootScope fv)
    (hfieldsList : 0 < u.size →
      (c.checkLCtx.toList.map (·.fvarId)).reverse =
        (stats.params ++ bu).toList.map (·.fvarId!))
    (hufields : ∀ j (hj : j < u.size), ∃ x ∈ bu.toList, x.fvarId! = u[j].fvarId!)
    (rootScopeInContext : ∀ fv, rootScope fv → fv ∈ R.mlctx.vlctx.fvars)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (fieldScope : Nat → FVarId → Prop)
    (HfieldsSharp : ∀ j (hj : j < u.size) fv, u[j] = .fvar fv →
      ∀ decl, c.lctx.find? fv = some decl → decl.type.FVarsIn (fieldScope j))
    (sharpInContext : ∀ j fv, fieldScope j fv → fv ∈ R.mlctx.vlctx.fvars)
    (hsharpUp : ∀ j, IsFVarUpSet (fieldScope j) R.mlctx.vlctx)
    (hrootUniverses : R.typeChecker.UniverseScope c.lparams rootScope)
    (hsharpUniverses : ∀ j, R.typeChecker.UniverseScope c.lparams (fieldScope j))
    (hfieldUniverses : ∀ j (hj : j < u.size) fv, u[j] = .fvar fv →
      ∀ decl, c.lctx.find? fv = some decl → decl.type.levelParamsIn c.lparams = true)
    (Happlications : RecInfoMotiveApplications R stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hshape : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (calls : Array AddInductive.RecCallTemplate),
      RecursorFVarSuffix R Rout values →
      (HoutOrigins : InductionHypothesisTypesPrefix
        stats recInfos c out u values) →
      CallTemplatesMatchPrefix HoutOrigins rootScope calls →
      TypedCallTemplates R decl depth stats
        (recInfos.map (·.motive)) rootScope u values calls →
      TypedCallTemplatesAt R decl depth stats
        (recInfos.map (·.motive)) fieldScope u values calls →
      values.size = u.size →
      calls.size = values.size →
      (k values calls out).WF Q) :
    (AddInductive.mkRecInfos.loopUTemplates stats bu u recInfos 0 #[] #[]
      k c).WF Q := by
  refine resultBindings stats bu u recInfos k R R rootScope
    rootScopeInContext hrootUp 0 #[] #[]
    (RecursorFVarSuffix.empty R)
    (InductionHypothesisTypesPrefix.empty stats recInfos c u)
    (CallTemplatesMatchPrefix.empty
      (InductionHypothesisTypesPrefix.empty stats recInfos c u) rootScope)
    (TypedCallTemplates.empty R decl depth stats
      (recInfos.map (·.motive)) rootScope u)
    fieldScope
    (TypedCallTemplatesAt.empty R decl depth stats
      (recInfos.map (·.motive)) fieldScope u)
    rfl rfl rfl rfl ?_ ?_
  intro next Rnext prior Hprior hcheckNext j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield, hfieldScope⟩
  have hpriorFVars : ∃ k,
      (AddInductive.mkRecInfos.fieldsBefore stats bu (.fvar fv)).toList.map
        (·.fvarId!) = ((next.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
      ((next.checkLCtx.toList.map (·.fvarId)).reverse)[k]? =
        some (Expr.fvar fv).fvarId! := by
    rw [hcheckNext, hfieldsList (by omega)]
    obtain ⟨x, hx, hxfv⟩ := hufields j hj
    rw [hfieldEq] at hxfv
    exact fieldsBefore_priorFVars stats bu fv ⟨x, hx, hxfv⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsNext := Hstats.weakenRecent Hprior
  have hctxNext : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  refine Except.WF.mono (Except.WF.and
    (inductionHypothesisTypeOrigin fv stats recInfos next
      Rnext HstatsNext hconsume
        (by simpa only [Hprior.venv_eq] using hlit) hctxNext HfieldAt
        _ hpriorFVars hfieldScope (Hprior.upsetRoot rootScopeInContext hrootUp)
        (by
          rw [Hprior.contextLE.lparams_eq]
          exact Hprior.universeScope rootScopeInContext hrootUniverses)
        (Hbindings.motives.mono Hprior.contextExtension.contextLE) hrecords
        ?happCoarse)
    (inductionHypothesisTypeOriginOfInferredScope fv stats recInfos next
      Rnext HstatsNext hconsume
        (by simpa only [Hprior.venv_eq] using hlit) hctxNext HfieldAt
        _ hpriorFVars
        ((getTypeFVarRun.WF next fv (by
            rcases Rnext.findCDecl HfieldAt.fvarsIn with ⟨_, _, _, _, _, h⟩
            exact ⟨_, h⟩)).mono fun _ ⟨decl, hfind, hty⟩ => by
          subst hty
          have hfvRoot : fv ∈ c.lctx.fvars := by
            rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq]
            simpa only [FVarsIn] using Hfield.fvarsIn
          rw [Hprior.contextLE.declarations fv hfvRoot] at hfind
          exact HfieldsSharp j hj fv hfieldEq decl hfind)
        (Hprior.upsetRoot (sharpInContext j) (hsharpUp j))
        ⟨by
          rw [Hprior.contextLE.lparams_eq]
          exact Hprior.universeScope (sharpInContext j) (hsharpUniverses j),
         fun ty hty => by
          obtain ⟨decl, hfind, rfl⟩ := getTypeFVarRun.WF next fv (by
            rcases Rnext.findCDecl HfieldAt.fvarsIn with ⟨_, _, _, _, _, h⟩
            exact ⟨_, h⟩) ty hty
          have hfvRoot : fv ∈ c.lctx.fvars := by
            rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq]
            simpa only [FVarsIn] using Hfield.fvarsIn
          rw [Hprior.contextLE.declarations fv hfvRoot] at hfind
          rw [Hprior.contextLE.lparams_eq]
          exact hfieldUniverses j hj fv hfieldEq decl hfind⟩
        (Hbindings.motives.mono Hprior.contextExtension.contextLE) hrecords
        ?happSharp)) ?combine
  case combine =>
    rintro result ⟨⟨viTarget, HviTr, HviType, O, hcall, Hsem⟩,
      ⟨_, _, _, _, _, Hsharp⟩⟩
    exact ⟨viTarget, HviTr, HviType, O, hcall, Hsem, Hsharp⟩
  case happCoarse | happSharp =>
    intro current Rcurrent exposedType syntaxTarget terminalTarget
      appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
      HappliedType hvalid
    let HstatsCurrent := HstatsNext.weakenRecent Hargs
    have htargetStats : target < stats.indConsts.size :=
      (checkPositivityStep.isValidIndApp?_some hvalid).1
    have htarget : target < recInfos.size := by
      rw [hrecords]
      exact htargetStats
    have htargetDecl : target < decl.types.length := by
      rw [← HstatsCurrent.types_size]
      exact htargetStats
    have hctxCurrent : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
      Hargs.noIndConsts (names := decl.types.map (·.name)) hctxNext
    let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
      htargetDecl
        (by simpa only [Hargs.venv_eq, Hprior.venv_eq] using hlit)
      hctxCurrent
    exact Happlications.applyAtMono Hbindings Horigins Hshape
      (Hprior.contextExtension.trans Hargs.contextExtension)
      target htarget Hexposed Hdefeq
      Hterminal Happlied HappliedType Hvalidated
  · intro out Rout values calls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics HvalueSharpSemantics hsize hcallSize
    apply Hk Rout values calls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics HvalueSharpSemantics
    · simpa using hsize
    · exact hcallSize

/-- Shared-telescope form of `resultTypingOfMotiveApplications`. -/
theorem resultTypingOfMotiveTelescopes
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (bu u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallTemplate →
      AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (rootScope : FVarId → Prop)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget ∧ rootScope fv)
    (hfieldsList : 0 < u.size →
      (c.checkLCtx.toList.map (·.fvarId)).reverse =
        (stats.params ++ bu).toList.map (·.fvarId!))
    (hufields : ∀ j (hj : j < u.size), ∃ x ∈ bu.toList, x.fvarId! = u[j].fvarId!)
    (rootScopeInContext : ∀ fv, rootScope fv → fv ∈ R.mlctx.vlctx.fvars)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (fieldScope : Nat → FVarId → Prop)
    (HfieldsSharp : ∀ j (hj : j < u.size) fv, u[j] = .fvar fv →
      ∀ decl, c.lctx.find? fv = some decl → decl.type.FVarsIn (fieldScope j))
    (sharpInContext : ∀ j fv, fieldScope j fv → fv ∈ R.mlctx.vlctx.fvars)
    (hsharpUp : ∀ j, IsFVarUpSet (fieldScope j) R.mlctx.vlctx)
    (hrootUniverses : R.typeChecker.UniverseScope c.lparams rootScope)
    (hsharpUniverses : ∀ j, R.typeChecker.UniverseScope c.lparams (fieldScope j))
    (hfieldUniverses : ∀ j (hj : j < u.size) fv, u[j] = .fvar fv →
      ∀ decl, c.lctx.find? fv = some decl → decl.type.levelParamsIn c.lparams = true)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hshape : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (calls : Array AddInductive.RecCallTemplate),
      RecursorFVarSuffix R Rout values →
      (HoutOrigins : InductionHypothesisTypesPrefix
        stats recInfos c out u values) →
      CallTemplatesMatchPrefix HoutOrigins rootScope calls →
      TypedCallTemplates R decl depth stats
        (recInfos.map (·.motive)) rootScope u values calls →
      TypedCallTemplatesAt R decl depth stats
        (recInfos.map (·.motive)) fieldScope u values calls →
      values.size = u.size →
      calls.size = values.size →
      (k values calls out).WF Q) :
    (AddInductive.mkRecInfos.loopUTemplates stats bu u recInfos 0 #[] #[]
      k c).WF Q :=
  resultTypingOfMotiveApplications stats bu u recInfos k R rootScope Hstats
    hconsume hlit hctx Hfields hfieldsList hufields rootScopeInContext hrootUp
    fieldScope HfieldsSharp sharpInContext hsharpUp
    hrootUniverses hsharpUniverses hfieldUniverses
    Htelescopes.applications Hbindings
    Horigins Hshape hrecords Hk

end mkRecInfos.loopUTemplates

/-- Equality of the four binder projections (motive, minors, indices and
major) of two `RecInfo` arrays of the same size.  Arrays related this way may
differ in their rule templates but have the same bindings, binder types and
telescopes. -/
structure RecInfoEqExceptRules (left right : Array AddInductive.RecInfo) : Prop where
  size_eq : left.size = right.size
  motive_eq_all : ∀ (i : Nat), left[i]!.motive = right[i]!.motive
  motive_eq : ∀ i (_hi : i < left.size),
    left[i]!.motive = right[i]!.motive
  minors_eq : ∀ i (_hi : i < left.size),
    left[i]!.minors = right[i]!.minors
  indices_eq : ∀ i (_hi : i < left.size),
    left[i]!.indices = right[i]!.indices
  major_eq : ∀ i (_hi : i < left.size),
    left[i]!.major = right[i]!.major

theorem RecInfoEqExceptRules.map_motive
    (H : RecInfoEqExceptRules left right) :
    left.map (·.motive) = right.map (·.motive) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.motive_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoEqExceptRules.map_major
    (H : RecInfoEqExceptRules left right) :
    left.map (·.major) = right.map (·.major) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.major_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoEqExceptRules.map_minors
    (H : RecInfoEqExceptRules left right) :
    left.map (·.minors) = right.map (·.minors) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.minors_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoEqExceptRules.map_indices
    (H : RecInfoEqExceptRules left right) :
    left.map (·.indices) = right.map (·.indices) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.indices_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

def MotiveBinding.congrInfo
    (B : MotiveBinding R info elimLevel)
    (hmotive : info.motive = info'.motive)
    (hindices : info.indices = info'.indices)
    (hmajor : info.major = info'.major) :
    MotiveBinding R info' elimLevel where
  motiveTarget := B.motiveTarget
  motiveTypeTarget := B.motiveTypeTarget
  motive := by simpa only [← hmotive] using B.motive
  motiveType := by
    simpa only [← hindices, ← hmajor] using B.motiveType
  typing := B.typing
  typeIsType := B.typeIsType

def MotiveAppliesTo.congrInfo
    (E : MotiveAppliesTo R stats info B exposedType
      syntaxTarget)
    (hmotive : info.motive = info'.motive)
    (hindices : info.indices = info'.indices)
    (hmajor : info.major = info'.major) :
    MotiveAppliesTo R stats info'
      (B.congrInfo hmotive hindices hmajor) exposedType syntaxTarget where
  indices := E.indices
  family := E.family
  familyActualType := E.familyActualType
  familyType := E.familyType
  motiveType := E.motiveType
  resultLevel := E.resultLevel
  syntax_eq := E.syntax_eq
  indices_translation := E.indices_translation
  family_typing := E.family_typing
  family_type_defeq := E.family_type_defeq
  motive_type_defeq := E.motive_type_defeq
  telescope := E.telescope

structure RecInfoEqOnFamilyBinders
    (left right : Array AddInductive.RecInfo) : Prop where
  map_motive : left.map (·.motive) = right.map (·.motive)
  motive_eq : ∀ (i : Nat), left[i]!.motive = right[i]!.motive
  indices_eq : ∀ (i : Nat), left[i]!.indices = right[i]!.indices
  major_eq : ∀ (i : Nat), left[i]!.major = right[i]!.major

theorem RecInfoEqOnFamilyBinders.size_eq
    (H : RecInfoEqOnFamilyBinders left right) : left.size = right.size := by
  have h := congrArg Array.size H.map_motive
  simpa using h

theorem MotiveTelescopesAt.rebaseMotiveCore
    (K : MotiveTelescopesAt R stats decl left elimLevel)
    (H : RecInfoEqOnFamilyBinders left right) :
    MotiveTelescopesAt R stats decl right elimLevel where
  rootBinding target htarget := by
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases K.rootBinding target htarget' with ⟨binding⟩
    exact ⟨binding.congrInfo (H.motive_eq target)
      (H.indices_eq target) (H.major_eq target)⟩
  appliesTo target htarget _current Rcurrent Hext _depth _exposedType
      _syntaxTarget Hexposed HsyntaxType Hvalidated := by
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases K.appliesTo target htarget' Rcurrent Hext Hexposed HsyntaxType
        Hvalidated with ⟨binding, ⟨evidence⟩⟩
    let binding' := binding.congrInfo (H.motive_eq target)
      (H.indices_eq target) (H.major_eq target)
    let evidence' := evidence.congrInfo (H.motive_eq target)
      (H.indices_eq target) (H.major_eq target)
    exact ⟨binding', ⟨evidence'⟩⟩

theorem TypedRuleTemplateAt.rebaseMotiveCore
    (Horigin : TypedRuleTemplateAt R decl stats left
      elimLevel parameterDecls expectedOwnerIdx S B)
    (H : RecInfoEqOnFamilyBinders left right) :
    TypedRuleTemplateAt R decl stats right elimLevel
      parameterDecls expectedOwnerIdx S B := by
  unfold TypedRuleTemplateAt at Horigin ⊢
  rcases Horigin with
    ⟨origins, hshape, hstats, hmotives, F, hparams, depth, HvalidStats,
      fields, Hselection, hexpectedValid, hexpectedLt, ownerIdx,
      htargetValid, Hvalidated, binding, ⟨Hevidence⟩,
      ⟨Hlookup⟩, Hcalls, Hsharp⟩
  let binding' := binding.congrInfo (H.motive_eq ownerIdx)
    (H.indices_eq ownerIdx) (H.major_eq ownerIdx)
  let evidence' := Hevidence.congrInfo (H.motive_eq ownerIdx)
    (H.indices_eq ownerIdx) (H.major_eq ownerIdx)
  have Hcalls' := Hcalls
  rw [H.map_motive] at Hcalls'
  have Hsharp' := Hsharp
  rw [H.map_motive] at Hsharp'
  exact ⟨origins, hshape, hstats, hmotives.trans H.map_motive,
    F, hparams, depth, HvalidStats, fields, Hselection, hexpectedValid,
    hexpectedLt, ownerIdx, htargetValid, Hvalidated,
    binding', ⟨evidence'⟩,
    ⟨Hlookup.rebaseMotiveCore H⟩, Hcalls', Hsharp'⟩

theorem RecInfoEqExceptRules.flatMap_minors
    (H : RecInfoEqExceptRules left right) :
    left.flatMap (·.minors) = right.flatMap (·.minors) := by
  apply Array.toList_inj.mp
  simpa [Array.toList_flatMap, Array.toList_map, List.flatMap_map] using
    congrArg (fun a : Array (Array Expr) =>
      a.toList.flatMap Array.toList) H.map_minors

theorem RecInfoEqExceptRules.flatMap_indices
    (H : RecInfoEqExceptRules left right) :
    left.flatMap (·.indices) = right.flatMap (·.indices) := by
  apply Array.toList_inj.mp
  simpa [Array.toList_flatMap, Array.toList_map, List.flatMap_map] using
    congrArg (fun a : Array (Array Expr) =>
      a.toList.flatMap Array.toList) H.map_indices

def FVarArrayIn.rebaseExprs
    (B : FVarArrayIn c xs) (h : xs = ys) : FVarArrayIn c ys where
  fvars := B.fvars
  expressions := h.symm.trans B.expressions
  members := B.members

def RecInfoBindings.rebaseCore
    (B : RecInfoBindings c left) (H : RecInfoEqExceptRules left right) :
    RecInfoBindings c right where
  motives := B.motives.rebaseExprs H.map_motive
  majors := B.majors.rebaseExprs H.map_major
  indices i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact (B.indices i hi').rebaseExprs (H.indices_eq i hi')
  minors i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact (B.minors i hi').rebaseExprs (H.minors_eq i hi')

theorem RecInfoBindings.rebaseCore_motives_fvars
    (B : RecInfoBindings c left) (H : RecInfoEqExceptRules left right) :
    (B.rebaseCore H).motives.fvars = B.motives.fvars := rfl

theorem RecInfoBindings.rebaseCore_flatMinors_fvars
    (B : RecInfoBindings c left) (H : RecInfoEqExceptRules left right) :
    (B.rebaseCore H).flatMinors.fvars = B.flatMinors.fvars := by
  calc
    (B.rebaseCore H).flatMinors.fvars =
        ExprArrayFVarIds (right.flatMap (·.minors)) :=
      ((B.rebaseCore H).flatMinors.exprArrayFVarIds).symm
    _ = ExprArrayFVarIds (left.flatMap (·.minors)) := by rw [H.flatMap_minors]
    _ = B.flatMinors.fvars := B.flatMinors.exprArrayFVarIds

theorem RecInfoBindings.NoAlias.rebaseCore
    (N : RecInfoBindings.NoAlias params left)
    (H : RecInfoEqExceptRules left right) :
    RecInfoBindings.NoAlias params right := by
  unfold RecInfoBindings.NoAlias RecInfoBindings.allFvars at N ⊢
  rw [← H.map_motive, ← H.map_major, ← H.flatMap_minors,
    ← H.flatMap_indices]
  exact N

theorem RecInfoOuterOrder.rebaseCore
    (B : RecInfoBindings c left)
    (O : RecInfoOuterOrder R params B) (H : RecInfoEqExceptRules left right) :
    RecInfoOuterOrder R params (B.rebaseCore H) := by
  unfold RecInfoOuterOrder at O ⊢
  simpa only [B.rebaseCore_motives_fvars H,
    B.rebaseCore_flatMinors_fvars H] using O

def RecInfoBinderTypes.rebaseCore
    (O : RecInfoBinderTypes c left) (H : RecInfoEqExceptRules left right) :
    RecInfoBinderTypes c right where
  motiveTypes := O.motiveTypes
  majorTypes := O.majorTypes
  indexTypes := O.indexTypes
  minorTypes := O.minorTypes
  indexTypes_size := O.indexTypes_size.trans H.size_eq
  minorTypes_size := O.minorTypes_size.trans H.size_eq
  motives := H.map_motive ▸ O.motives
  majors := H.map_major ▸ O.majors
  indices i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    rw [← H.indices_eq i hi']
    exact O.indices i hi'
  minors i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    rw [← H.minors_eq i hi']
    exact O.minors i hi'
  minorShapes i hi j hj := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact O.minorShapes i hi' j hj

theorem MajorPremiseTypes.rebaseCore
    (S : MajorPremiseTypes stats left majorTypes ok)
    (H : RecInfoEqExceptRules left right) :
    MajorPremiseTypes stats right majorTypes ok := by
  refine ⟨S.size_eq.trans H.size_eq, ?_⟩
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi']
  exact S.shape i hi'

theorem MotiveTypes.rebaseCore
    (S : MotiveTypes c left motiveTypes elimLevel)
    (H : RecInfoEqExceptRules left right) :
    MotiveTypes c right motiveTypes elimLevel := by
  refine ⟨S.size_eq.trans H.size_eq, ?_⟩
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi', ← H.major_eq i hi']
  exact S.shape i hi'

theorem RecInfoMotiveTelescopes.rebaseCore
    (T : RecInfoMotiveTelescopes R stats decl parameterCtx left elimLevel)
    (H : RecInfoEqExceptRules left right) :
    RecInfoMotiveTelescopes R stats decl parameterCtx right elimLevel := by
  refine ⟨?_, ?_, ?_⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    apply MotiveAppliesAbove.congrInfo (T.telescope target htarget')
    · exact (H.motive_eq target htarget').symm
    · exact (H.indices_eq target htarget').symm
    · exact (H.major_eq target htarget').symm
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.motiveDecls target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target htarget').symm
      (H.major_eq target htarget').symm
    exact ⟨S', by
      simpa [S', MotiveDecl.congrInfo] using hparams⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.motiveDecls target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target htarget').symm
      (H.major_eq target htarget').symm
    exact ⟨S'.canonical, by
      simpa [S', MotiveDecl.congrInfo] using hparams⟩

theorem RecInfoArities.rebaseCore
    (A : RecInfoArities stats left) (H : RecInfoEqExceptRules left right) :
    RecInfoArities stats right := by
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi']
  exact A i hi'

theorem MinorPremiseType.HasInductionHypothesisTypes.rebaseCore
    (S : MinorPremiseType)
    (P : MinorPremiseType.HasInductionHypothesisTypes S stats left)
    (H : RecInfoEqExceptRules left right) :
    MinorPremiseType.HasInductionHypothesisTypes S stats right := by
  unfold MinorPremiseType.HasInductionHypothesisTypes at P ⊢
  cases hopt : S.hypothesis_type_origins with
  | none => simp [hopt] at P
  | some origins =>
      simp only [hopt] at P ⊢
      exact ⟨P.1, P.2.trans H.map_motive⟩

theorem TypedMinors.rebaseCore
    (O : RecInfoBinderTypes c left)
    (A : TypedMinors R O parameterDecls)
    (H : RecInfoEqExceptRules left right) :
    TypedMinors R (O.rebaseCore H) parameterDecls := by
  intro owner howner localIndex hlocal
  have howner' : owner < left.size := by simpa [H.size_eq] using howner
  simpa [RecInfoBinderTypes.rebaseCore] using
    A owner howner' localIndex hlocal

theorem MinorsMatchConstructors.rebaseCore
    (O : RecInfoBinderTypes c left)
    (A : MinorsMatchConstructors stats indTypes O)
    (H : RecInfoEqExceptRules left right) :
    MinorsMatchConstructors stats indTypes (O.rebaseCore H) := by
  intro owner howner hsourceOwner localIndex hlocal
  have howner' : owner < left.size := by simpa [H.size_eq] using howner
  rcases A owner howner' hsourceOwner localIndex hlocal with
    ⟨horigin, hindex, hsource, hhypotheses, traversal, htraversal,
      hctor, hfields, hrecursive, hstats, hvalid, hmotive,
      hroot, hterminal, hfull⟩
  refine ⟨horigin, hindex, hsource,
    MinorPremiseType.HasInductionHypothesisTypes.rebaseCore _
      hhypotheses H,
    traversal, htraversal, hctor, hfields, hrecursive, hstats, hvalid,
    ?_, hroot, hterminal, hfull⟩
  rcases hindices : AddInductive.getIIndices stats traversal.terminal with
    ⟨motiveOwner, indices⟩
  change (O.minorShapes owner howner' localIndex hlocal).motiveApp =
    Expr.app (mkAppN right[motiveOwner]!.motive indices)
      (mkAppN
        (mkAppN (.const
          (O.minorShapes owner howner' localIndex hlocal).constructor.name
            stats.levels) stats.params)
        (O.minorShapes owner howner' localIndex hlocal).fields)
  rw [← H.motive_eq_all]
  simpa only [hindices] using hmotive

theorem MinorsAndIndicesMatchSource.rebaseCore
    (O : RecInfoBinderTypes c left)
    (A : MinorsAndIndicesMatchSource stats indTypes O)
    (H : RecInfoEqExceptRules left right) :
    MinorsAndIndicesMatchSource stats indTypes (O.rebaseCore H) :=
  ⟨MinorsMatchConstructors.rebaseCore O A.rows H,
    A.traces.congr H.size_eq H.indices_eq⟩

theorem modifyMinorAndTemplate_coreEq
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (hidx : dIdx < recInfos.size) (minor : Expr)
    (blueprint : AddInductive.RecRuleTemplate) :
    RecInfoEqExceptRules
      (recInfos.modify dIdx fun info =>
        { info with minors := info.minors.push minor })
      (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleTemplates := info.ruleTemplates.push blueprint }) := by
  constructor
  · simp
  · intro i
    by_cases hi : i < recInfos.size
    · by_cases hself : dIdx = i
      · subst i
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hself]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hself]
    · simp [hi]
  all_goals
    intro i hi
    have hi' : i < recInfos.size := by simpa using hi
    by_cases hself : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi' hself]
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi' hself]

theorem modifyMinorAndTemplate_motiveCoreEq
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (minor : Expr) (blueprint : AddInductive.RecRuleTemplate) :
    RecInfoEqOnFamilyBinders recInfos
      (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleTemplates := info.ruleTemplates.push blueprint }) := by
  let next := recInfos.modify dIdx fun info =>
    { info with
      minors := info.minors.push minor
      ruleTemplates := info.ruleTemplates.push blueprint }
  have hfield : ∀ (i : Nat),
      recInfos[i]!.motive = next[i]!.motive ∧
      recInfos[i]!.indices = next[i]!.indices ∧
      recInfos[i]!.major = next[i]!.major := by
    intro i
    by_cases hi : i < recInfos.size
    · by_cases hself : dIdx = i
      · subst i
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
        simp
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi
          hself]
        simp
    · have hiNext : ¬ i < next.size := by simpa [next] using hi
      simp [hi, hiNext]
  refine {
    map_motive := ?_
    motive_eq := fun i => (hfield i).1
    indices_eq := fun i => (hfield i).2.1
    major_eq := fun i => (hfield i).2.2 }
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hiLeft' : i < recInfos.size := by simpa using hiLeft
    have hiRight' : i < next.size := by
      dsimp [next]
      simpa using hiRight
    rw [Array.getElem_map, Array.getElem_map]
    have h := (hfield i).1
    rw [getElem!_pos recInfos i hiLeft', getElem!_pos next i hiRight'] at h
    exact h

namespace mkRecInfos.loopCtors

/-- Inserting the minor premise for the current constructor at the end of row
`dIdx` keeps the rule-template rows the same length as the minor-type rows,
given that the old rows had equal lengths. -/
theorem continueMinor_rowsSize
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkTemplate : Expr → AddInductive.RecRuleTemplate)
    (Horigins : RecInfoBinderTypes c recInfos)
    (hidx : dIdx < recInfos.size)
    (HminorShape : MinorPremiseType)
    (Hrows : ∀ owner, owner < recInfos.size →
      recInfos[owner]!.ruleTemplates.size =
        Horigins.minorTypes[owner]!.size) :
    let cMinor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName minorTy .default }
    let next := recInfos.modify dIdx fun info =>
      { info with
        minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
        ruleTemplates := info.ruleTemplates.push
          (mkTemplate (.fvar ⟨c.ngen.curr⟩)) }
    let Hcore := modifyMinorAndTemplate_coreEq recInfos dIdx hidx
      (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
    let HoriginsMinor := Horigins.addMinor dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName minorTy
      .default HminorShape
    let HoriginsNext : RecInfoBinderTypes cMinor next :=
      HoriginsMinor.rebaseCore Hcore
    ∀ owner, owner < next.size →
      next[owner]!.ruleTemplates.size =
        HoriginsNext.minorTypes[owner]!.size := by
  intro cMinor next Hcore HoriginsMinor HoriginsNext
  intro owner howner
  have hownerOld : owner < recInfos.size := by
    simpa [next] using howner
  by_cases hdi : dIdx = owner
  · subst owner
    have hrow := Hrows dIdx hidx
    have hminorSize := (Horigins.minors dIdx hidx).size_eq
    have hidxTypes : dIdx < Horigins.minorTypes.size := by
      rw [Horigins.minorTypes_size]
      exact hidx
    dsimp [next, HoriginsNext, HoriginsMinor,
      RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    rw [mkRecInfos.loopCtors.getElemBang_modify_self Horigins.minorTypes
      dIdx _ hidxTypes]
    simp only [Array.size_push]
    omega
  · have hrow := Hrows owner hownerOld
    have hownerTypes : owner < Horigins.minorTypes.size := by
      rw [Horigins.minorTypes_size]
      exact hownerOld
    dsimp [next, HoriginsNext, HoriginsMinor,
      RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
    rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
      hownerOld hdi]
    rw [mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
      dIdx owner _ hownerTypes hdi]
    exact hrow

/-- Every field binder of every minor row stays distinct from the
recursor prefix after the current constructor's minor premise is opened as a
fresh local and appended to row `dIdx`.  Old rows use the old freshness fact
`Hfresh`; the new row uses `HminorFieldsFresh`; the fresh minor itself is not
among any field binders because those are already in the context. -/
theorem continueMinor_fieldsOuterFresh
    (stats : AddInductive.InductiveStats)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkTemplate : Expr → AddInductive.RecRuleTemplate)
    (Horigins : RecInfoBinderTypes c recInfos)
    (hidx : dIdx < recInfos.size)
    (HminorShape : MinorPremiseType)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {parameterDecls : VLCtx}
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (HminorSemantic :
      Nonempty (TypedMinorTraversalAt R HminorShape parameterDecls))
    (HminorFieldsFresh : ∀ fv ∈ HminorShape.fields_bound.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars)
    (Hfresh : ∀ owner (howner : owner < recInfos.size) (localIndex : Nat)
      (hlocal : localIndex < Horigins.minorTypes[owner]!.size) (fv : FVarId),
      fv ∈ (Horigins.minorShapes owner howner localIndex
        hlocal).fields_bound.fvars →
      fv ∉ (ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (recInfos.map (·.motive))) ++
        ExprArrayFVarIds (recInfos.flatMap (·.minors))) :
    let cMinor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName minorTy .default }
    let next := recInfos.modify dIdx fun info =>
      { info with
        minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
        ruleTemplates := info.ruleTemplates.push
          (mkTemplate (.fvar ⟨c.ngen.curr⟩)) }
    let Hcore := modifyMinorAndTemplate_coreEq recInfos dIdx hidx
      (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
    let HoriginsMinor := Horigins.addMinor dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName minorTy
      .default HminorShape
    let HoriginsNext : RecInfoBinderTypes cMinor next :=
      HoriginsMinor.rebaseCore Hcore
    ∀ owner (howner : owner < next.size) (localIndex : Nat)
      (hlocal : localIndex < HoriginsNext.minorTypes[owner]!.size)
      (fv : FVarId),
      fv ∈ (HoriginsNext.minorShapes owner howner localIndex
        hlocal).fields_bound.fvars →
      fv ∉ (ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (next.map (·.motive))) ++
        ExprArrayFVarIds (next.flatMap (·.minors)) := by
  intro cMinor next Hcore HoriginsMinor HoriginsNext
  let HbindingsMinor := Hbindings.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName minorTy .default
  let HbindingsNext : RecInfoBindings cMinor next :=
    HbindingsMinor.rebaseCore Hcore
  have hmotivesNext : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiNext hiOld
      rw [Array.getElem_map, Array.getElem_map]
      rw [Array.getElem_modify (by simpa [next] using hiNext)]
      split <;> rfl
  have hflatMinorsFVarsNext : HbindingsNext.flatMinors.fvars =
      Hbindings.flatMinors.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)] := by
    change (HbindingsMinor.rebaseCore Hcore).flatMinors.fvars = _
    rw [HbindingsMinor.rebaseCore_flatMinors_fvars Hcore]
    exact Hbindings.addMinor_flatMinors_fvars dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy .default Hlater
  intro owner howner localIndex hlocal fv hfv
  have hownerOld : owner < recInfos.size := by
    simpa [next] using howner
  rw [hmotivesNext, Hparams.exprArrayFVarIds,
    Hbindings.motives.exprArrayFVarIds,
    HbindingsNext.flatMinors.exprArrayFVarIds,
    hflatMinorsFVarsNext]
  intro houter
  have holdOrCurrent :
      fv ∈ (Hparams.fvars ++ Hbindings.motives.fvars) ++
          Hbindings.flatMinors.fvars ∨
        fv = (⟨c.ngen.curr⟩ : FVarId) := by
    rcases List.mem_append.mp houter with hpm | hminorCurrent
    · exact Or.inl (List.mem_append.mpr (Or.inl hpm))
    · rcases List.mem_append.mp hminorCurrent with hminor | hcurrent
      · exact Or.inl (List.mem_append.mpr (Or.inr hminor))
      · exact Or.inr (by simpa using hcurrent)
  rcases holdOrCurrent with holdOuter | hcurrent
  · by_cases hdi : dIdx = owner
    · subst owner
      by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
      · subst localIndex
        have hshapeLast :
            HoriginsNext.minorShapes dIdx howner
                Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
        rw [hshapeLast] at hfv
        exact HminorFieldsFresh fv hfv holdOuter
      · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
          dsimp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore,
            RecInfoBinderTypes.addMinor] at hlocal
          have hidxTypes : dIdx < Horigins.minorTypes.size := by
            rw [Horigins.minorTypes_size]
            exact hidx
          rw [mkRecInfos.loopCtors.getElemBang_modify_self
            Horigins.minorTypes dIdx _ hidxTypes] at hlocal
          simp only [Array.size_push] at hlocal
          omega
        have hshapeOld :
            HoriginsNext.minorShapes dIdx howner localIndex hlocal =
              Horigins.minorShapes dIdx hidx localIndex hold := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
            hlast]
        rw [hshapeOld] at hfv
        apply Hfresh dIdx hidx
          localIndex hold fv hfv
        simpa only [Hparams.exprArrayFVarIds,
          Hbindings.motives.exprArrayFVarIds,
          Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
    · have hlocalOld :
          localIndex < Horigins.minorTypes[owner]!.size := by
        simpa [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
            dIdx owner _
              (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
          using hlocal
      have hshapeOld :
          HoriginsNext.minorShapes owner howner localIndex hlocal =
            Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          hdi]
      rw [hshapeOld] at hfv
      apply Hfresh owner hownerOld
        localIndex hlocalOld fv hfv
      simpa only [Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds,
        Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
  · subst fv
    apply R.toBindingContextWF.current_not_mem
    by_cases hdi : dIdx = owner
    · subst owner
      by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
      · subst localIndex
        have hshapeLast :
            HoriginsNext.minorShapes dIdx howner
                Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
        rw [hshapeLast] at hfv
        rcases HminorSemantic with ⟨HS⟩
        exact HS.semantic.extension.contextLE.fvars
          (HminorShape.fields_bound.members _ hfv)
      · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
          dsimp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore,
            RecInfoBinderTypes.addMinor] at hlocal
          have hidxTypes : dIdx < Horigins.minorTypes.size := by
            rw [Horigins.minorTypes_size]
            exact hidx
          rw [mkRecInfos.loopCtors.getElemBang_modify_self
            Horigins.minorTypes dIdx _ hidxTypes] at hlocal
          simp only [Array.size_push] at hlocal
          omega
        have hshapeOld :
            HoriginsNext.minorShapes dIdx howner localIndex hlocal =
              Horigins.minorShapes dIdx hidx localIndex hold := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
            hlast]
        rw [hshapeOld] at hfv
        rcases HminorSemantics dIdx hidx localIndex hold with ⟨HS⟩
        exact HS.semantic.extension.contextLE.fvars
          ((Horigins.minorShapes dIdx hidx localIndex hold
            ).fields_bound.members _ hfv)
    · have hlocalOld :
          localIndex < Horigins.minorTypes[owner]!.size := by
        simpa [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
            dIdx owner _
              (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
          using hlocal
      have hshapeOld :
          HoriginsNext.minorShapes owner howner localIndex hlocal =
            Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          hdi]
      rw [hshapeOld] at hfv
      rcases HminorSemantics owner hownerOld localIndex hlocalOld with ⟨HS⟩
      exact HS.semantic.extension.contextLE.fvars
        ((Horigins.minorShapes owner hownerOld localIndex hlocalOld
          ).fields_bound.members _ hfv)

/-- The syntactic rule-template alignment `RuleTemplatesMatch` survives inserting
the current constructor's minor premise and its template at the end of row `dIdx`. -/
theorem continueMinor_templateOrigins
    (stats : AddInductive.InductiveStats)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkTemplate : Expr → AddInductive.RecRuleTemplate)
    (Horigins : RecInfoBinderTypes c recInfos)
    (hidx : dIdx < recInfos.size)
    (HminorShape : MinorPremiseType)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {parameterDecls : VLCtx}
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (HminorSemantic :
      Nonempty (TypedMinorTraversalAt R HminorShape parameterDecls))
    (HminorFieldsFresh : ∀ fv ∈ HminorShape.fields_bound.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HminorTemplate : RuleTemplateMatchesMinor stats
      HminorShape (.fvar ⟨c.ngen.curr⟩)
      (mkTemplate (.fvar ⟨c.ngen.curr⟩))) :
    let cMinor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName minorTy .default }
    let next := recInfos.modify dIdx fun info =>
      { info with
        minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
        ruleTemplates := info.ruleTemplates.push
          (mkTemplate (.fvar ⟨c.ngen.curr⟩)) }
    let Hcore := modifyMinorAndTemplate_coreEq recInfos dIdx hidx
      (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
    let HoriginsMinor := Horigins.addMinor dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName minorTy
      .default HminorShape
    let HoriginsNext : RecInfoBinderTypes cMinor next :=
      HoriginsMinor.rebaseCore Hcore
    RuleTemplatesMatch stats next HoriginsNext := by
  intro cMinor next Hcore HoriginsMinor HoriginsNext
  refine {
    rows_size := continueMinor_rowsSize R dIdx recInfos minorName minorTy
      mkTemplate Horigins hidx HminorShape
      Hblueprints.rows_size
    entry := ?_
    fields_outer_fresh := continueMinor_fieldsOuterFresh stats R dIdx recInfos minorName minorTy
      mkTemplate Horigins hidx HminorShape Hbindings Hparams
      Hlater HminorSemantics HminorSemantic HminorFieldsFresh
      Hblueprints.fields_outer_fresh }
  intro owner howner localIndex hlocal
  have hownerOld : owner < recInfos.size := by
    simpa [next] using howner
  by_cases hdi : dIdx = owner
  · subst owner
    by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
    · subst localIndex
      have hminorIndex : Horigins.minorTypes[dIdx]!.size =
          recInfos[dIdx]!.minors.size :=
        (Horigins.minors dIdx hidx).size_eq
      have hblueprintIndex : Horigins.minorTypes[dIdx]!.size =
          recInfos[dIdx]!.ruleTemplates.size :=
        (Hblueprints.rows_size dIdx hidx).symm
      have hminorLast :
          (recInfos[dIdx]!.minors.push (.fvar ⟨c.ngen.curr⟩))[
            Horigins.minorTypes[dIdx]!.size]! =
            .fvar ⟨c.ngen.curr⟩ := by
        rw [hminorIndex]
        simp
      have hblueprintLast :
          (recInfos[dIdx]!.ruleTemplates.push
            (mkTemplate (.fvar ⟨c.ngen.curr⟩)))[
              Horigins.minorTypes[dIdx]!.size]! =
            mkTemplate (.fvar ⟨c.ngen.curr⟩) := by
        rw [hblueprintIndex]
        simp
      have hshapeLast :
          HoriginsNext.minorShapes dIdx howner
            Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
      rw [hshapeLast]
      simpa [next, HoriginsNext, HoriginsMinor,
        RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
        RuleTemplateMatchesMinor,
        mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
        hminorLast, hblueprintLast]
        using HminorTemplate
    · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
        dsimp [HoriginsNext, HoriginsMinor, RecInfoBinderTypes.rebaseCore,
          RecInfoBinderTypes.addMinor] at hlocal
        have hidxTypes : dIdx < Horigins.minorTypes.size := by
          rw [Horigins.minorTypes_size]
          exact hidx
        rw [mkRecInfos.loopCtors.getElemBang_modify_self
          Horigins.minorTypes dIdx _ hidxTypes] at hlocal
        simp only [Array.size_push] at hlocal
        omega
      have holdMinor : localIndex < recInfos[dIdx]!.minors.size := by
        rw [← (Horigins.minors dIdx hidx).size_eq]
        exact hold
      have holdTemplate :
          localIndex < recInfos[dIdx]!.ruleTemplates.size := by
        rw [Hblueprints.rows_size dIdx hidx]
        exact hold
      have holdMinor' : localIndex < recInfos[dIdx].minors.size := by
        simpa [getElem!_pos recInfos dIdx hidx] using holdMinor
      have holdBlueprint' :
          localIndex < recInfos[dIdx].ruleTemplates.size := by
        simpa [getElem!_pos recInfos dIdx hidx] using holdTemplate
      have hminorGet :
          (recInfos[dIdx]!.minors.push
            (.fvar ⟨c.ngen.curr⟩))[localIndex]! =
            recInfos[dIdx]!.minors[localIndex]! := by
        simp [Array.getElem!_eq_getD, Array.getD, hidx, holdMinor',
          Array.getElem_push_lt holdMinor']; omega
      have hblueprintGet :
          (recInfos[dIdx]!.ruleTemplates.push
            (mkTemplate (.fvar ⟨c.ngen.curr⟩)))[localIndex]! =
            recInfos[dIdx]!.ruleTemplates[localIndex]! := by
        simp [Array.getElem!_eq_getD, Array.getD, hidx, holdBlueprint',
          Array.getElem_push_lt holdBlueprint']; omega
      have Hentry := Hblueprints.entry dIdx hidx localIndex hold
      have hshapeOld :
          HoriginsNext.minorShapes dIdx howner localIndex hlocal =
            Horigins.minorShapes dIdx hidx localIndex hold := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          hlast]
      rw [hshapeOld]
      simpa [next, HoriginsNext, HoriginsMinor,
        RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
        RuleTemplateMatchesMinor,
        mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
        hlast, Array.getElem_push_lt hold,
        Array.getElem_push_lt holdMinor,
        Array.getElem_push_lt holdTemplate,
        hminorGet, hblueprintGet] using Hentry
  · have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
      simpa [HoriginsNext, HoriginsMinor, RecInfoBinderTypes.rebaseCore,
        RecInfoBinderTypes.addMinor,
        mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
          dIdx owner _ (by simpa [Horigins.minorTypes_size] using hownerOld)
          hdi] using hlocal
    have Hentry := Hblueprints.entry owner hownerOld localIndex hlocalOld
    have hshapeOld :
        HoriginsNext.minorShapes owner howner localIndex hlocal =
          Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
      simp [HoriginsNext, HoriginsMinor,
        RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor, hdi]
    rw [hshapeOld]
    simpa [next, HoriginsNext, HoriginsMinor,
      RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
      RuleTemplateMatchesMinor,
      hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
        hownerOld hdi] using Hentry

/-- The typed rule-template rows `TypedRuleTemplates` survive opening the
current constructor's minor premise as a local and inserting it with its template
at the end of row
`dIdx`: old entries are transported along the context extension, and the new
entry is `HminorTemplateTyped`. -/
theorem continueMinor_templateSemanticOrigins
    (stats : AddInductive.InductiveStats)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {elimLevel : Level}
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkTemplate : Expr → AddInductive.RecRuleTemplate)
    (Horigins : RecInfoBinderTypes c recInfos)
    (hidx : dIdx < recInfos.size)
    (HminorShape : MinorPremiseType)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {parameterDecls : VLCtx}
    (HminorSemantics : TypedMinors R Horigins
      parameterDecls)
    (HminorSemantic :
      Nonempty (TypedMinorTraversalAt R HminorShape parameterDecls))
    (HminorFieldsFresh : ∀ fv ∈ HminorShape.fields_bound.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars)
    {minorTarget : VExpr}
    (Hminor : TrExprS R.venv recLparams R.mlctx.vlctx minorTy minorTarget)
    (HminorType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx minorTarget)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (HminorTemplateTyped : Nonempty
      (TypedRuleTemplateAt R decl stats recInfos elimLevel
        parameterDecls dIdx HminorShape
        (mkTemplate (.fvar ⟨c.ngen.curr⟩)))) :
    let cMinor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName minorTy .default }
    let next := recInfos.modify dIdx fun info =>
      { info with
        minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
        ruleTemplates := info.ruleTemplates.push
          (mkTemplate (.fvar ⟨c.ngen.curr⟩)) }
    let Hcore := modifyMinorAndTemplate_coreEq recInfos dIdx hidx
      (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
    let HoriginsMinor := Horigins.addMinor dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName minorTy
      .default HminorShape
    let HoriginsNext : RecInfoBinderTypes cMinor next :=
      HoriginsMinor.rebaseCore Hcore
    let Rminor := R.withLocalDecl (name := minorName) (bi := .default)
      Hminor HminorType
    TypedRuleTemplates Rminor decl stats next elimLevel
      parameterDecls HoriginsNext := by
  intro cMinor next Hcore HoriginsMinor HoriginsNext Rminor
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := .default) R Hminor HminorType
  let HmotiveCore := modifyMinorAndTemplate_motiveCoreEq recInfos dIdx hidx
    (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
  have hmotivesNext : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiNext hiOld
      rw [Array.getElem_map, Array.getElem_map]
      rw [Array.getElem_modify (by simpa [next] using hiNext)]
      split <;> rfl
  refine {
    rows_size := continueMinor_rowsSize R dIdx recInfos minorName minorTy
      mkTemplate Horigins hidx HminorShape
      HblueprintSemantics.rows_size
    entry := ?_
    fields_outer_fresh := continueMinor_fieldsOuterFresh stats R dIdx recInfos minorName minorTy
      mkTemplate Horigins hidx HminorShape Hbindings Hparams
      Hlater HminorSemantics HminorSemantic HminorFieldsFresh
      HblueprintSemantics.fields_outer_fresh }
  intro owner howner localIndex hlocal
  have hownerOld : owner < recInfos.size := by
    simpa [next] using howner
  by_cases hdi : dIdx = owner
  · subst owner
    by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
    · subst localIndex
      have hblueprintIndex : Horigins.minorTypes[dIdx]!.size =
          recInfos[dIdx]!.ruleTemplates.size :=
        (HblueprintSemantics.rows_size dIdx hidx).symm
      have hblueprintLast :
          (recInfos[dIdx]!.ruleTemplates.push
            (mkTemplate (.fvar ⟨c.ngen.curr⟩)))[
              Horigins.minorTypes[dIdx]!.size]! =
            mkTemplate (.fvar ⟨c.ngen.curr⟩) := by
        rw [hblueprintIndex]
        simp
      have hshapeLast :
          HoriginsNext.minorShapes dIdx howner
            Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor]
      rw [hshapeLast]
      rcases HminorTemplateTyped with ⟨HminorTemplateTyped⟩
      have HminorBlueprintSemantic' :=
        (HminorTemplateTyped.mono Hstep).rebaseMotiveCore HmotiveCore
      simpa [next, Rminor, TypedRuleTemplateAt,
        mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
        hblueprintLast, hmotivesNext] using HminorBlueprintSemantic'
    · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
        dsimp [HoriginsNext, HoriginsMinor, RecInfoBinderTypes.rebaseCore,
          RecInfoBinderTypes.addMinor] at hlocal
        have hidxTypes : dIdx < Horigins.minorTypes.size := by
          rw [Horigins.minorTypes_size]
          exact hidx
        rw [mkRecInfos.loopCtors.getElemBang_modify_self
          Horigins.minorTypes dIdx _ hidxTypes] at hlocal
        simp only [Array.size_push] at hlocal
        omega
      have holdTemplate :
          localIndex < recInfos[dIdx]!.ruleTemplates.size := by
        rw [HblueprintSemantics.rows_size dIdx hidx]
        exact hold
      have holdBlueprint' :
          localIndex < recInfos[dIdx].ruleTemplates.size := by
        simpa [getElem!_pos recInfos dIdx hidx] using holdTemplate
      have hblueprintGet :
          (recInfos[dIdx]!.ruleTemplates.push
            (mkTemplate (.fvar ⟨c.ngen.curr⟩)))[localIndex]! =
            recInfos[dIdx]!.ruleTemplates[localIndex]! := by
        simp [Array.getElem!_eq_getD, Array.getD, hidx, holdBlueprint',
          Array.getElem_push_lt holdBlueprint']; omega
      rcases HblueprintSemantics.entry dIdx hidx localIndex hold with ⟨Hentry⟩
      have Hentry := (Hentry.mono Hstep).rebaseMotiveCore HmotiveCore
      have hshapeOld :
          HoriginsNext.minorShapes dIdx howner localIndex hlocal =
            Horigins.minorShapes dIdx hidx localIndex hold := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor,
          hlast]
      rw [hshapeOld]
      simpa [next, Rminor, TypedRuleTemplateAt,
        mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
        hlast, Array.getElem_push_lt holdTemplate, hblueprintGet,
        hmotivesNext] using
          Hentry
  · have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
      simpa [HoriginsNext, HoriginsMinor, RecInfoBinderTypes.rebaseCore,
        RecInfoBinderTypes.addMinor,
        mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
          dIdx owner _ (by simpa [Horigins.minorTypes_size] using hownerOld)
          hdi] using hlocal
    rcases HblueprintSemantics.entry owner hownerOld localIndex
      hlocalOld with ⟨Hentry⟩
    have Hentry := (Hentry.mono Hstep).rebaseMotiveCore HmotiveCore
    have hshapeOld :
        HoriginsNext.minorShapes owner howner localIndex hlocal =
          Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
      simp [HoriginsNext, HoriginsMinor,
        RecInfoBinderTypes.rebaseCore, RecInfoBinderTypes.addMinor, hdi]
    rw [hshapeOld]
    simpa [next, Rminor, TypedRuleTemplateAt, hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
        hownerOld hdi, hmotivesNext] using Hentry

/-- Typing of the final action of one constructor iteration.
Once the complete minor domain has been translated and typed,
this mirrors the executable's `withLocalDecl`, updates the owning minor row, and
transports every invariant of the recursor frames into the new context. -/
theorem continueMinorTyping {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkTemplate : Expr → AddInductive.RecRuleTemplate)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos
      Horigins.majorTypes c.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn c stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {minorTarget : VExpr}
    (Hminor : TrExprS R.venv recLparams R.mlctx.vlctx
      (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) minorTarget)
    (HminorType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx minorTarget)
    (HminorShape : MinorPremiseType)
    (HminorShapePosition :
      HminorShape.localIndex = Horigins.minorTypes[dIdx]!.size ∧
      HminorShape.origin = (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper))
    (HminorSource : HminorShape.sourceConstructors =
      indTypes[dIdx]!.ctors)
    (HminorHypothesisOrigins :
      HminorShape.HasInductionHypothesisTypes stats recInfos)
    (HminorSemantic :
      Nonempty (TypedMinorTraversalAt R HminorShape
        Hsuffix.parameterDecls))
    (HminorFieldsFresh : ∀ fv ∈ HminorShape.fields_bound.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars)
    (HminorTraversal : ∃ traversal,
      HminorShape.traversal = some traversal ∧
      traversal.constructor = HminorShape.constructor ∧
      traversal.fields = HminorShape.fields ∧
      traversal.recursiveFields = HminorShape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      HminorShape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const HminorShape.constructor.name stats.levels)
              stats.params)
            HminorShape.fields)) ∧
      BindingContextLE traversal.rootContext c ∧
      BindingContextLE traversal.terminalContext c ∧
      BindingContextLE HminorShape.sourceFullContext c)
    (HminorTemplate : RuleTemplateMatchesMinor stats
      HminorShape (.fvar ⟨c.ngen.curr⟩)
      (mkTemplate (.fvar ⟨c.ngen.curr⟩)))
    (HminorTemplateTyped : Nonempty
      (TypedRuleTemplateAt R decl stats recInfos elimLevel
        Hsuffix.parameterDecls dIdx HminorShape
        (mkTemplate (.fvar ⟨c.ngen.curr⟩))))
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (_henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (_hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (_HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (_hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoBinderTypes outCtx out),
      RuleTemplatesMatch stats out HoriginsOut →
      TypedRuleTemplates Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      MinorsAndIndicesMatchSource stats indTypes HoriginsOut →
      TypedMinors Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (withLocalDecl minorName .default (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
      (fun minor =>
        let next := recInfos.modify dIdx fun info =>
          { info with
            minors := info.minors.push minor
            ruleTemplates := info.ruleTemplates.push (mkTemplate minor) }
        k next) c).WF Q := by
  refine withLocalDecl.recursorWF (name := minorName) (bi := .default)
    R Hminor HminorType ?_
  let Rminor := R.withLocalDecl (name := minorName) (bi := .default)
    Hminor HminorType
  let cMinor : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName
      (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default }
  let next := recInfos.modify dIdx fun info =>
    { info with
      minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
      ruleTemplates := info.ruleTemplates.push
        (mkTemplate (.fvar ⟨c.ngen.curr⟩)) }
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := .default) R Hminor HminorType
  let HbindingsMinor := Hbindings.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default
  let HoriginsMinor := Horigins.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default HminorShape
  let HminorSourcesMinor := HminorSources.addMinor dIdx hidx hsourceIdx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
    (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default HminorShape
    HminorShapePosition HminorSource HminorHypothesisOrigins HminorTraversal
  let HminorSemanticsMinor := HminorSemantics.addMinor
    (RecursorContextExtension.refl R) dIdx hidx minorName
    (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default Hminor HminorType HminorShape
    HminorSemantic
  let Hcore := modifyMinorAndTemplate_coreEq recInfos dIdx hidx
    (.fvar ⟨c.ngen.curr⟩) (mkTemplate (.fvar ⟨c.ngen.curr⟩))
  let HbindingsNext : RecInfoBindings cMinor next :=
    HbindingsMinor.rebaseCore Hcore
  let HoriginsNext : RecInfoBinderTypes cMinor next :=
    HoriginsMinor.rebaseCore Hcore
  let HparamsMinor := Hparams.mono Hstep.contextLE
  have HblueprintsNext :
      RuleTemplatesMatch stats next HoriginsNext :=
    continueMinor_templateOrigins stats R dIdx recInfos minorName
      _ mkTemplate Horigins hidx HminorShape Hbindings
      Hparams Hlater HminorSemantics HminorSemantic HminorFieldsFresh
      Hblueprints HminorTemplate
  have HblueprintSemanticsNext :
      TypedRuleTemplates Rminor decl stats next elimLevel
        Hsuffix.parameterDecls HoriginsNext :=
    continueMinor_templateSemanticOrigins stats R dIdx recInfos minorName
      _ mkTemplate Horigins hidx HminorShape Hbindings
      Hparams Hlater HminorSemantics HminorSemantic HminorFieldsFresh
      Hminor HminorType HblueprintSemantics HminorTemplateTyped
  have HminorSourcesNext :
      MinorsAndIndicesMatchSource stats indTypes HoriginsNext := by
    exact MinorsAndIndicesMatchSource.rebaseCore _ HminorSourcesMinor Hcore
  have HminorSemanticsNext :
      TypedMinors Rminor HoriginsNext
        Hsuffix.parameterDecls := by
    exact TypedMinors.rebaseCore _ HminorSemanticsMinor Hcore
  have HorderMinor : RecInfoOuterOrder Rminor HparamsMinor
      HbindingsMinor := by
    refine RecInfoOuterOrder.addMinor
      (minor := (⟨c.ngen.curr⟩ : FVarId)) Horder ?_ ?_ ?_ ?_
    · rfl
    · exact Hbindings.addMinor_motives_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default
    · exact Hbindings.addMinor_flatMinors_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          (minorTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) .default Hlater
    · rfl
  have HorderNext : RecInfoOuterOrder Rminor HparamsMinor HbindingsNext :=
    RecInfoOuterOrder.rebaseCore HbindingsMinor HorderMinor Hcore
  refine Hk next Rminor rfl (Hsuffix.withAmbient Hminor HminorType) rfl
    (Hstats.withFVar Rminor.checking.tr.wf Rminor.mlctx_wf.tr.wf)
    (VLCtx.NoIndConsts.cons hctx rfl)
    HbindingsNext HoriginsNext HblueprintsNext HblueprintSemanticsNext
      HminorSourcesNext
      HminorSemanticsNext
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      HparamsMinor ?_ ?_ ?_ ?_
  · simp [next]
  · dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    simp
  · intro i hi hine
    dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hine]
  · change TrBinderTypes Rminor Horigins.majorTypes
    simpa [Rminor] using HmajorTypes.mono Hstep
  · exact (HmajorShapes.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · change TrBinderTypes Rminor Horigins.motiveTypes
    simpa [Rminor] using HmotiveTypes.mono Hstep
  · exact ((HmotiveShapes.mono Hbindings Hstep.contextLE).modifyMinors
      dIdx (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · exact ((Htelescopes.mono Hstep).modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · change TrBinderTypesPerFamily Rminor Horigins.indexTypes
    simpa [Rminor] using HindexRows.mono Hstep
  · exact RecInfoBindings.NoAlias.rebaseCore
      (Hbindings.addMinor_noAlias Hparams HnoAlias dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF) Hcore
  · exact HorderNext
  · exact (Harities.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · exact Hroot.trans Hstep.contextLE

/-- The sharpened scope of a recursive field (the fields opened before it,
together with the common parameters) is upward closed in the field context,
given that the full field-and-parameter scope is. -/
theorem constructorFieldPrefixScopeUp
    {c current : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Rargs : RecursorContextWF current recLparams}
    {stats : AddInductive.InductiveStats} {allFields : Array Expr}
    (HfieldsRecent : RecursorFVarSuffix R Rargs allFields)
    (Hparams : FVarArrayIn c stats.params)
    (hfieldsUp : IsFVarUpSet
      (fun fv => fv ∈ HfieldsRecent.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params) Rargs.mlctx.vlctx)
    (field : Expr) :
    IsFVarUpSet (RecursorFieldPrefixScope stats.params HfieldsRecent.fvars
      field) Rargs.mlctx.vlctx := by
  have hsplit := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    Rargs.mlctx allFields.size HfieldsRecent.size_le
  rw [HfieldsRecent.drop_eq] at hsplit
  have hprefix : VLCtx.fvars (Rargs.mlctx.vlctx.take allFields.size) =
      HfieldsRecent.fvars.reverse := by
    rw [TypeChecker.MLCtx.vlctx_take_fvars]
    exact HfieldsRecent.fvarRevList_eq
  have hwf : VLCtx.FVWF
      (Rargs.mlctx.vlctx.take allFields.size ++ R.mlctx.vlctx) := by
    rw [← hsplit]
    exact Rargs.mlctx_wf.tr.wf.fvwf
  have hfresh : ∀ fv ∈ HfieldsRecent.fvars,
      ¬ fv ∈ ExprArrayFVarIds stats.params := by
    intro fv hfv hparam
    apply HfieldsRecent.toFVarArrayAfter.fresh fv hfv
    apply Hparams.members
    rw [← Hparams.exprArrayFVarIds]
    exact hparam
  have hup : IsFVarUpSet
      (fun fv => fv ∈ HfieldsRecent.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      (Rargs.mlctx.vlctx.take allFields.size ++ R.mlctx.vlctx) := by
    rw [← hsplit]
    exact hfieldsUp
  have hsharp := IsFVarUpSet.sharpenPrefix _ _ _ hwf hprefix hfresh hup
    (HfieldsRecent.fvars.idxOf (recursorFVarId field))
  rw [← hsplit] at hsharp
  exact hsharp

/-- Closing a translated body first over the generated induction hypotheses
and then over the constructor fields yields a well-typed translated minor
premise type in the outer recursor context. -/
theorem constructorMinorTypeTranslation
    {c current outCtx : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Rargs : RecursorContextWF current recLparams}
    {Rout : RecursorContextWF outCtx recLparams}
    {allFields hypotheses : Array Expr} {body : Expr} {bodyTarget : VExpr}
    (HfieldsRecent : RecursorFVarSuffix R Rargs allFields)
    (HhypothesesRecent : RecursorFVarSuffix Rargs Rout hypotheses)
    (Hbody : TrExprS Rout.venv recLparams Rout.mlctx.vlctx body bodyTarget)
    (HbodyType : Rout.venv.IsType recLparams.length Rout.mlctx.vlctx.toCtx
      bodyTarget) :
    ∃ minorTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        (outCtx.lctx.mkForall allFields
          (outCtx.lctx.mkForall hypotheses body)) minorTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx minorTarget := by
  rcases HhypothesesRecent.mkForall Hbody HbodyType with
    ⟨hypothesesTarget, Hhypotheses, HhypothesesType⟩
  rcases HfieldsRecent.mkForall Hhypotheses HhypothesesType with
    ⟨minorTarget, HminorRaw, HminorRawType⟩
  refine ⟨minorTarget, ?_, HminorRawType⟩
  rw [HfieldsRecent.toFVarArrayAfter.toFVarArrayIn.mkForall_mono
    HhypothesesRecent.contextLE _]
  exact HminorRaw

/-- A motive application `motive indices arg` for a recorded family has an
outer motive binder of the recursor prefix as its head. -/
theorem motiveApplicationHeadRoot
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    {owner : Nat} (howner : owner < recInfos.size)
    (indices : Array Expr) (arg : Expr) :
    ∃ fv,
      (Expr.app (mkAppN recInfos[owner]!.motive indices) arg).getAppFn =
        .fvar fv ∧
      fv ∈ R.mlctx.vlctx.fvars := by
  have hownerMotive : owner < (recInfos.map (·.motive)).size := by
    simpa using howner
  rcases Hbindings.motives.getElem_eq_fvar owner hownerMotive with
    ⟨hmotiveFVars, hmotiveSource⟩
  let motiveFVar := Hbindings.motives.fvars[owner]
  have hmotiveBang : recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos recInfos owner howner]
    simpa [motiveFVar] using hmotiveSource
  refine ⟨motiveFVar, ?_, ?_⟩
  · simp [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotiveBang]
  · apply Horder.subset
    apply List.mem_reverse.mpr
    simp [motiveFVar, List.getElem_mem hmotiveFVars]

/-- The generated induction-hypothesis binders are distinct from the common
parameters and the motive binders of the recursor prefix. -/
theorem inductionHypothesesOuterFresh
    {c current outCtx : AddInductive.Context} {recLparams : List Name}
    {Rargs : RecursorContextWF current recLparams}
    {Rout : RecursorContextWF outCtx recLparams}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo} {hypotheses : Array Expr}
    (Hparams : FVarArrayIn c stats.params)
    (Hbindings : RecInfoBindings c recInfos)
    (hle : BindingContextLE c current)
    (HhypothesesRecent : RecursorFVarSuffix Rargs Rout hypotheses) :
    ∀ fv,
      fv ∈ ExprArrayFVarIds stats.params ++
          ExprArrayFVarIds (recInfos.map (·.motive)) →
        fv ∉ ExprArrayFVarIds hypotheses := by
  intro fv houter hhypothesis
  rw [Hparams.exprArrayFVarIds,
    Hbindings.motives.exprArrayFVarIds] at houter
  rw [(HhypothesesRecent.toFVarArrayAfter.toFVarArrayIn
    ).exprArrayFVarIds] at hhypothesis
  apply HhypothesesRecent.toFVarArrayAfter.fresh fv hhypothesis
  apply hle.fvars
  rcases List.mem_append.mp houter with hparam | hmotive
  · exact Hparams.members fv hparam
  · exact Hbindings.motives.members fv hmotive

/-- Freshly opened constructor fields are distinct from every binder of the
recursor prefix: parameters, motives and the minors added so far. -/
theorem constructorFieldsOuterFresh
    {c current : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Rargs : RecursorContextWF current recLparams}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo} {allFields : Array Expr}
    (HfieldsRecent : RecursorFVarSuffix R Rargs allFields)
    (Hparams : FVarArrayIn c stats.params)
    (Hbindings : RecInfoBindings c recInfos) :
    ∀ fv ∈ HfieldsRecent.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars := by
  intro fv hfield houter
  apply HfieldsRecent.toFVarArrayAfter.fresh fv hfield
  rcases List.mem_append.mp houter with hpm | hminor
  · rcases List.mem_append.mp hpm with hparam | hmotive
    · exact Hparams.members fv hparam
    · exact Hbindings.motives.members fv hmotive
  · exact Hbindings.flatMinors.members fv hminor

/-- The call templates recorded while generating the induction hypotheses
match (`CallTemplatesMatch`) any induction-hypothesis type table with the same
statistics, records and field root. -/
theorem CallTemplatesMatch.ofHypothesisCalls
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {current outCtx : AddInductive.Context}
    {recursiveFields hypotheses allFields : Array Expr}
    {calls : Array AddInductive.RecCallTemplate}
    {HhypothesisOrigins : InductionHypothesisTypesPrefix stats recInfos current
      outCtx recursiveFields hypotheses}
    {fieldFVars : List FVarId}
    (hids : ExprArrayFVarIds allFields = fieldFVars)
    (HhypothesisCallOrigins : CallTemplatesMatchPrefix
      HhypothesisOrigins
      (fun fv => fv ∈ fieldFVars ∨ fv ∈ ExprArrayFVarIds stats.params) calls)
    (origins : MinorInductionHypothesisTypes outCtx recursiveFields
      hypotheses)
    (hstats : origins.stats = stats) (hrecInfos : origins.recInfos = recInfos)
    (hroot : origins.fieldRoot = current) :
    CallTemplatesMatch origins allFields calls := by
  cases origins
  cases hstats
  cases hrecInfos
  cases hroot
  refine {
    size_eq := HhypothesisCallOrigins.size_eq
    entry := ?_
    rooted := ?_ }
  · intro j hj
    rcases HhypothesisCallOrigins.entry j hj with
      ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
    exact ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
  · intro j hj
    rcases HhypothesisCallOrigins.rooted j hj with
      ⟨originRoot, sourceType, recL, Rorigin, O, D, HoriginRoot, hup,
        htype, hcall⟩
    refine ⟨originRoot, sourceType, recL, Rorigin, O, D, HoriginRoot, ?_,
      htype, hcall⟩
    rw [hids]
    exact hup

/-- Final step of one constructor iteration in the minor pass of `mkRecInfos`.
Given the opened constructor fields, the checked owner application of the
terminal type, its motive application, and the generated induction
hypotheses with their call templates, the minor premise closed over fields
and hypotheses is translated, typed and inserted into row `dIdx`, and every
minor-pass invariant is handed to the continuation `k`. -/
theorem constructorMinorClosureTyping {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctor : Constructor) (tail : Expr)
    (sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hsourceConstructor : sourceConstructors[sourceIndex]? = some ctor)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tailTarget : VExpr}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : ParameterPrefix stats 0 ctor.type tail)
    (htailScope : tail.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params))
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (htailType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx tailTarget)
    {tailTarget₀ : VExpr}
    (htail₀ : TrExprS R.venv recLparams Hsuffix.parameterDecls tail tailTarget₀)
    (htail₀Ty : R.venv.IsType recLparams.length Hsuffix.parameterDecls.toCtx
      tailTarget₀)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos
      Horigins.majorTypes c.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn c stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (_henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (_hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (_HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (_hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoBinderTypes outCtx out),
      RuleTemplatesMatch stats out HoriginsOut →
      TypedRuleTemplates Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      MinorsAndIndicesMatchSource stats indTypes HoriginsOut →
      TypedMinors Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q)
    {current : AddInductive.Context}
    (Rargs : RecursorContextWF current recLparams)
    {terminal : Expr} {terminalTarget : VExpr}
    {allFields recursiveFields : Array Expr}
    {fields : List (RecursiveFieldDomainAt Rargs.venv decl
      recLparams.length)}
    {positions : List Nat}
    (HterminalNonforall : terminal.isForall = false)
    (Hterminal : TrExprS Rargs.venv recLparams Rargs.mlctx.vlctx
      terminal terminalTarget)
    (HterminalType : Rargs.venv.IsType recLparams.length
      Rargs.mlctx.vlctx.toCtx terminalTarget)
    (Hselections : RecursiveFieldSelectionsAt Rargs.venv decl
      recLparams.length allFields recursiveFields fields)
    (Hdecisions : RecursorFieldDecisions stats c tail current terminal
      allFields recursiveFields positions)
    (HfieldsRecent : RecursorFVarSuffix R Rargs allFields)
    (Hopening : ConstructorFieldOpening tail terminal allFields)
    (HfieldTargetDefEq : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx tailTarget
      (Rargs.mlctx.mkForall' allFields.size HfieldsRecent.size_le
        terminalTarget))
    (HfieldParameterUp : IsFVarUpSet
      (fun fv => fv ∈ HfieldsRecent.fvars ∨ fv ∈ ExprArrayFVarIds stats.params)
      Rargs.mlctx.vlctx)
    (hfieldCheck : ∃ M : TypeChecker.MLCtx,
      M.WF Rargs.venv recLparams ∧
      (0 < allFields.size → Rargs.chk = M) ∧
      ∃ hn : allFields.size ≤ M.length,
        MLCtxTopAgree Rargs.mlctx M allFields.size ∧
          (M.dropN allFields.size hn).vlctx = Hsuffix.parameterDecls ∧
          ∃ t₀', TrExprS Rargs.venv recLparams M.vlctx terminal t₀' ∧
            Rargs.venv.IsDefEqU recLparams.length
              Hsuffix.parameterDecls.toCtx tailTarget₀
              (M.mkForall' allFields.size hn t₀'))
    (hdidxValid : AddInductive.isValidIndAppIdx stats terminal dIdx = true)
    (hdidxDecl : dIdx < decl.types.length)
    (Happlication : ConstructorApplicationAt Rargs stats ctor
      terminal allFields terminalTarget)
    (htarget : Happlication.ownerIdx < recInfos.size)
    (Hvalidated : RecursorValidatedIndAppAt Rargs.venv recLparams
      Rargs.mlctx.vlctx stats decl (depth + allFields.size)
      terminal terminalTarget Happlication.ownerIdx)
    (Hbinding : MotiveBinding Rargs recInfos[Happlication.ownerIdx]!
      elimLevel)
    (HmotiveEvidence : Nonempty (MotiveAppliesTo Rargs stats
      recInfos[Happlication.ownerIdx]! Hbinding terminal terminalTarget))
    {indices : Array Expr} {motiveTarget : VExpr}
    (Hmotive : TrExprS Rargs.venv recLparams Rargs.mlctx.vlctx
      (Expr.app
        (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
        (mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields))
      motiveTarget)
    (HmotiveType : Rargs.venv.IsType recLparams.length
      Rargs.mlctx.vlctx.toCtx motiveTarget)
    (howner : AddInductive.getIIndices stats terminal =
      (Happlication.ownerIdx, indices))
    {outCtx : AddInductive.Context}
    (Rout : RecursorContextWF outCtx recLparams)
    (hypotheses : Array Expr) (calls : Array AddInductive.RecCallTemplate)
    (HhypothesesRecent : RecursorFVarSuffix Rargs Rout hypotheses)
    (HhypothesisOrigins : InductionHypothesisTypesPrefix stats recInfos current
      outCtx recursiveFields hypotheses)
    (HhypothesisCallOrigins : CallTemplatesMatchPrefix
      HhypothesisOrigins
      (fun fv => fv ∈ HfieldsRecent.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params) calls)
    (HhypothesisCallSemantics : TypedCallTemplates Rargs
      decl (depth + allFields.size) stats (recInfos.map (·.motive))
      (fun fv => fv ∈ HfieldsRecent.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      recursiveFields hypotheses calls)
    (HhypothesisCallSharpSemantics : TypedCallTemplatesAt
      Rargs decl (depth + allFields.size) stats (recInfos.map (·.motive))
      (fun j => RecursorFieldPrefixScope stats.params HfieldsRecent.fvars
        recursiveFields[j]!)
      recursiveFields hypotheses calls)
    (hhypothesesSize : hypotheses.size = recursiveFields.size) :
    ((do
      let lctx ← getLCtx
      let motiveApp := Expr.app
        (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
        (mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
      let minorTy := lctx.mkForall allFields <|
        lctx.mkForall hypotheses motiveApp
      let minorName := ctor.name.replacePrefix indTypeName .anonymous
      AddInductive.withUnannotatedLocalDecl minorName .default minorTy
          fun minor =>
        let next := recInfos.modify dIdx fun info =>
          { info with
            minors := info.minors.push minor
            ruleTemplates := info.ruleTemplates.push {
              ctor := ctor.name
              fields := allFields
              lctx := lctx
              recursiveCalls := calls
              targetTypeIdx := Happlication.ownerIdx
              targetIndices := indices
              minor := minor } }
        k next : AddInductive.M alpha) outCtx).WF Q := by
  let HextArgs := HfieldsRecent.contextExtension
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  let HbindingsArgs := Hbindings.mono HextArgs.contextLE
  let HoriginsArgs := Horigins.mono HextArgs.contextLE
  let HmotiveShapesArgs := HmotiveShapes.mono Hbindings HextArgs.contextLE
  let HtelescopesArgs := Htelescopes.mono HextArgs
  let HextAll := HextArgs.trans HhypothesesRecent.contextExtension
  have HmotiveAt : TrExprS Rout.venv recLparams Rout.mlctx.vlctx
      (Expr.app
        (mkAppN recInfos[Happlication.ownerIdx]!.motive
          indices)
        (mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields))
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakTrExprS Hmotive
  have HmotiveTypeAt : Rout.venv.IsType recLparams.length
      Rout.mlctx.vlctx.toCtx
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakIsType HmotiveType
  obtain ⟨minorTarget, HminorRaw', HminorRawType⟩ :=
    constructorMinorTypeTranslation HfieldsRecent HhypothesesRecent
      HmotiveAt HmotiveTypeAt
  have hget : ((getLCtx : AddInductive.M LocalContext) outCtx).WF
      (fun lctx => lctx = outCtx.lctx) := by
    intro lctx h
    cases h
    rfl
  refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
    hget fun lctx hlctx => ?_
  subst lctx
  have HminorRawAt := HextAll.weakTrExprS HminorRaw'
  have HminorRawTypeAt := HextAll.weakIsType HminorRawType
  rcases hconsume outCtx recLparams Rout HminorRawAt HminorRawTypeAt with
    ⟨consumedTarget, Hconsumed⟩
  let HsuffixOut :=
    (Hsuffix.weakenRecent HfieldsRecent).weakenRecent HhypothesesRecent
  let HstatsOut := HstatsArgs.weakenRecent HhypothesesRecent
  have hctxOut : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rout.mlctx.vlctx :=
    HhypothesesRecent.noIndConsts
      (names := decl.types.map (·.name)) hctxArgs
  let traversal : ConstructorFieldTraversal := {
    constructor := ctor
    rootContext := c
    terminalContext := current
    terminal := terminal
    fields := allFields
    recursiveFields := recursiveFields
    stats := stats
    recursivePositions := positions
    decisions := Hdecisions
    recursivePositions_ordered := Hdecisions.positions_ordered
    recursivePositions_lt := Hdecisions.positions_lt
    recursivePositions_length := Hdecisions.positions_length
    parameterTail := tail
    parameterTail_fvars := by
      apply htailScope.mono
      intro fv hfv
      rw [Hparams.exprArrayFVarIds] at hfv
      exact Hparams.members fv hfv
    parameterPrefix := hprefix
    fieldFVars := Hopening.fvars
    fields_eq := Hopening.expressions
    fieldFVars_nodup := Hopening.nodup
    fieldResidual := Hopening.residual
    fieldTelescope := Hopening.telescope
    fieldClosed := Hopening.closed
    fieldResidual_not_forall := by
      rw [← Hopening.closed, Expr.abstractList_isForall]
      exact HterminalNonforall }
  let HbindingsOut := Hbindings.mono HextAll.contextLE
  let HoriginsOut := Horigins.mono HextAll.contextLE
  let HparamsOut := Hparams.mono HextAll.contextLE
  have HorderArgs := Horder.monoRecent HfieldsRecent
  have HorderOut0 := HorderArgs.monoRecent HhypothesesRecent
  have HorderOut : RecInfoOuterOrder Rout HparamsOut HbindingsOut := by
    unfold RecInfoOuterOrder at HorderOut0 ⊢
    change (Hparams.fvars ++ Hbindings.motives.fvars ++
      Hbindings.flatMinors.fvars).reverse <+ Rout.mlctx.vlctx.fvars
    exact HorderOut0
  let HminorSemanticsOut := HminorSemantics.mono HextAll
  let HcompletedOrigins : MinorInductionHypothesisTypes
      outCtx recursiveFields hypotheses := {
    stats := stats
    recInfos := recInfos
    fieldRoot := current
    fieldRoot_wf := Rargs.toBindingContextWF
    hypotheses_outer_fresh := inductionHypothesesOuterFresh Hparams Hbindings
      HextArgs.contextLE HhypothesesRecent
    entry := by
      intro j hj
      rcases HhypothesisOrigins.entry j hj with
        ⟨originRoot, sourceType, HoriginRoot, ⟨O⟩, D, htype⟩
      exact ⟨originRoot, sourceType, HoriginRoot, ⟨O.toMinor⟩, D, htype⟩ }
  have HcompletedCalls :
      CallTemplatesMatch HcompletedOrigins allFields calls :=
    CallTemplatesMatch.ofHypothesisCalls
      HfieldsRecent.toFVarArrayAfter.toFVarArrayIn.exprArrayFVarIds
      HhypothesisCallOrigins HcompletedOrigins rfl rfl rfl
  let motiveApp := Expr.app
    (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
    (mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
  let minorSourceType :=
    outCtx.lctx.mkForall allFields (outCtx.lctx.mkForall hypotheses motiveApp)
  refine continueMinorTyping (Q := Q) stats indTypes dIdx recInfos
    (ctor.name.replacePrefix indTypeName .anonymous) minorSourceType
    (fun minor => {
      ctor := ctor.name
      fields := allFields
      lctx := outCtx.lctx
      recursiveCalls := calls
      targetTypeIdx := Happlication.ownerIdx
      targetIndices := indices
      minor := minor })
    k Rout HsuffixOut HstatsOut hctxOut HbindingsOut HoriginsOut
      (Hblueprints.mono HextAll.contextLE)
      (HblueprintSemantics.mono HextAll)
      (HminorSources.mono HextAll.contextLE)
      HminorSemanticsOut
      (HmajorTypes.mono HextAll)
      (by rw [HextAll.contextLE.env_eq]; exact HmajorShapes)
      (HmotiveTypes.mono HextAll)
      (HmotiveShapes.mono Hbindings HextAll.contextLE)
      (Htelescopes.mono HextAll) (HindexRows.mono HextAll)
      HparamsOut
      HnoAlias
      HorderOut (Hroot.trans HextAll.contextLE) hidx hsourceIdx Harities
      Hlater Hconsumed.unannotated
      Hconsumed.isType {
        localIndex := HoriginsOut.minorTypes[dIdx]!.size
        origin := minorSourceType.consumeTypeAnnotationsVerified
          outCtx.env.isTypeAnnotationWrapper
        constructor := ctor
        sourceConstructors := sourceConstructors
        sourceConstructor := by
          simpa [HoriginsOut, RecInfoBinderTypes.mono, horiginIndex] using
            hsourceConstructor
        sourceFullContext := outCtx
        sourceFullWF := Rout.toBindingContextWF
        sourceContext := outCtx.lctx
        sourceContext_eq := rfl
        fields := allFields
        fields_bound :=
          HfieldsRecent.toFVarArrayAfter.toFVarArrayIn.mono
            HhypothesesRecent.contextExtension.contextLE
        fields_nodup := HfieldsRecent.toFVarArrayAfter.nodup
        recursiveFields := recursiveFields
        hypotheses := hypotheses
        hypotheses_bound :=
          HhypothesesRecent.toFVarArrayAfter.toFVarArrayIn
        hypotheses_nodup :=
          HhypothesesRecent.toFVarArrayAfter.nodup
        hypotheses_fields_fresh := by
          intro fv hhypothesis hfield
          apply HhypothesesRecent.toFVarArrayAfter.fresh fv
            hhypothesis
          exact HfieldsRecent.toFVarArrayAfter.toFVarArrayIn.members
            fv hfield
        hypothesis_type_origins := some HcompletedOrigins
        hypotheses_size := hhypothesesSize
        traversal := some traversal
        hypothesis_origins_fieldRoot := by
          intro origins' T horigins htraversal
          simp only [Option.some.injEq] at horigins htraversal
          subst origins'
          subst T
          rfl
        motiveApp := motiveApp
        sourceType := minorSourceType
        sourceType_eq := rfl
        unannotated_eq := rfl } ⟨rfl, rfl⟩ (by
          simpa [HoriginsOut, RecInfoBinderTypes.mono, horiginIndex] using
            hsourceFamily)
      (by exact ⟨rfl, rfl⟩)
      ⟨{
        semantic := {
          sourceWF := Rout
          extension := RecursorContextExtension.refl Rout
          traversal := traversal
          traversal_eq := rfl
          traversal_fields := rfl
          rootWF := R
          terminalWF := Rargs
          parameterDepth := depth
          parameterSuffix := Hsuffix
          parameterScope := by
            apply htailScope.mono
            intro fv hfv
            rw [Hsuffix.parameterDecls_fvars]
            simpa using hfv
          parameterTarget := tailTarget
          parameterTranslation := htail
          parameterType := htailType
          parameterTranslation₀ := ⟨_, htail₀⟩
          fieldsRecent := HfieldsRecent
          fieldCheck := by
            obtain ⟨M, hMwf, hchkM, hnM, hagM, hdropM, t₀', ht₀', hroot₀⟩ :=
              hfieldCheck
            exact ⟨M, hMwf, hchkM, hnM, hagM, hdropM, _, htail₀, t₀', ht₀',
              hroot₀⟩
          fieldOpening := Hopening
          fieldParameterUp := HfieldParameterUp
          hypothesesRecent := HhypothesesRecent
          terminalTarget := terminalTarget
          terminalTranslation := Hterminal
          terminalType := HterminalType
          constructorApplication := Happlication
          fieldTargetDefEq := HfieldTargetDefEq
          motivePreTarget := motiveTarget
          motivePreTranslation := Hmotive
          motivePreType := HmotiveType
          motiveHeadRoot :=
            motiveApplicationHeadRoot Hbindings Hparams Horder htarget _ _
          motiveTarget := motiveTarget.lift'
            (HhypothesesRecent.contextExtension.shift.consN 0)
          motiveTranslation := HmotiveAt
          motiveType := HmotiveTypeAt
          sourceTarget := minorTarget.lift' (HextAll.shift.consN 0)
          unannotatedTarget := consumedTarget
          consumption := Hconsumed }
        parameterDecls_eq := rfl }⟩
      (constructorFieldsOuterFresh HfieldsRecent Hparams Hbindings)
      ⟨traversal, rfl, rfl, rfl, rfl, rfl, by
        rw [howner]
        exact Happlication.owner_valid, by rw [howner],
        HextAll.contextLE,
        HhypothesesRecent.contextExtension.contextLE,
        BindingContextLE.refl outCtx⟩
      (by
        refine ⟨rfl, rfl, rfl, rfl, traversal, HcompletedOrigins,
          rfl, rfl, ?_, ?_, HcompletedCalls⟩
        · rw [howner]
        · rw [howner])
      (by
        refine ⟨HcompletedOrigins, rfl, rfl, rfl, {
          traversal := traversal
          traversal_eq := rfl
          traversal_constructor := rfl
          traversal_fields := rfl
          traversal_recursiveFields := rfl
          traversal_stats := rfl
          rootWF := R
          terminalWF := Rargs
          parameterDepth := depth
          parameterSuffix := Hsuffix
          terminalExtension := HhypothesesRecent.contextExtension
          fieldsRecent := HfieldsRecent
          parameterTarget := tailTarget
          parameterTail_params := htailScope
          parameterTranslation := htail
          parameterType := htailType
          parameterTranslation₀ := ⟨_, htail₀, htail₀Ty⟩
          fieldOpening := Hopening
          fieldParameterUp := HfieldParameterUp
          fieldCheck := by
            obtain ⟨M, hMwf, hchkM, hnM, hagM, hdropM, t₀', ht₀', hroot₀⟩ :=
              hfieldCheck
            exact ⟨M, hMwf, hchkM, hnM, hagM, hdropM, _, htail₀, t₀', ht₀',
              hroot₀⟩
          terminalTarget := terminalTarget
          terminalTranslation := Hterminal
          terminalType := HterminalType
          constructorApplication := Happlication
          fieldTargetDefEq := HfieldTargetDefEq }, rfl,
          depth + allFields.size, HstatsArgs, fields, Hselections,
          hdidxValid, hdidxDecl,
          Happlication.ownerIdx,
          Happlication.owner_valid, ⟨Hvalidated⟩,
          Hbinding, HmotiveEvidence,
          ⟨MotiveTelescopesAt.of HtelescopesArgs HbindingsArgs
            HoriginsArgs HmotiveShapesArgs⟩, ⟨?_⟩, ⟨?_⟩⟩
        · simpa using HhypothesisCallSemantics
        · simpa using HhypothesisCallSharpSemantics) ?_
  intro nextCtx nextDepth next Rnext henvNext HsuffixNext
    hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
    HblueprintsNext HblueprintSemanticsNext HminorSourcesNext
    HminorSemanticsNext
    hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext
    HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
    HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
  exact Hk next Rnext (henvNext.trans HextAll.venv_eq) HsuffixNext
    (hparameterDeclsNext.trans (by rfl)) HstatsNext hctxNext
    HbindingsNext HoriginsNext HblueprintsNext HblueprintSemanticsNext
    HminorSourcesNext
    HminorSemanticsNext
    hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext HmotiveTypesNext HmotiveShapesNext
    HtelescopesNext HindexRowsNext HparamsNext HnoAliasNext HorderNext
    HaritiesNext HrootNext

/-- Refinement of one constructor iteration in the minor pass of
`mkRecInfos`.  The only constructor-specific premise is the typing of the
constructor applied to the parameters (`Hintro`, `HintroType`) at
`tailTarget`; all recursive-field motives, generated IH binders, telescope
closure, and minor insertion are derived here. -/
theorem oneConstructorTyping {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctor : Constructor) (tail : Expr)
    (sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hsourceConstructor : sourceConstructors[sourceIndex]? = some ctor)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tailTarget : VExpr}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : ParameterPrefix stats 0 ctor.type tail)
    (htailScope : tail.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params))
    (hparamUniverses : ParameterUniverseSupport c stats.params)
    (htailUniverses : tail.levelParamsIn c.lparams = true)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (htailType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx tailTarget)
    {tailTarget₀ : VExpr}
    (htail₀ : TrExprS R.venv recLparams Hsuffix.parameterDecls tail tailTarget₀)
    (htail₀Ty : R.venv.IsType recLparams.length Hsuffix.parameterDecls.toCtx
      tailTarget₀)
    {introTarget : VExpr}
    (Hintro : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN (.const ctor.name stats.levels) stats.params) introTarget)
    (HintroType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos
      Horigins.majorTypes c.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn c stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hnormal : Nonempty
      (ConstructorOwnerNormalForm stats dIdx tail))
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (_henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (_hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (_HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (_hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoBinderTypes outCtx out),
      RuleTemplatesMatch stats out HoriginsOut →
      TypedRuleTemplates Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      MinorsAndIndicesMatchSource stats indTypes HoriginsOut →
      TypedMinors Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type
      (fun terminal allFields recursiveFields =>
        let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
        let introApp := mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields
        let motiveApp := Expr.app
          (mkAppN recInfos[ownerIdx]!.motive indices) introApp
        AddInductive.mkRecInfos.loopUTemplates stats allFields recursiveFields recInfos
          0 #[] #[] fun hypotheses calls => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall allFields <|
              lctx.mkForall hypotheses motiveApp
            let minorName :=
              ctor.name.replacePrefix indTypeName .anonymous
            AddInductive.withUnannotatedLocalDecl minorName .default minorTy fun minor =>
              let next := recInfos.modify dIdx fun info =>
                { info with
                  minors := info.minors.push minor
                  ruleTemplates := info.ruleTemplates.push {
                    ctor := ctor.name
                    fields := allFields
                    lctx := lctx
                    recursiveCalls := calls
                    targetTypeIdx := ownerIdx
                    targetIndices := indices
                    minor := minor } }
              k next) c).WF Q := by
  let process := fun terminal allFields recursiveFields =>
    let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
    let introApp := mkAppN
      (mkAppN (.const ctor.name stats.levels) stats.params) allFields
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive indices) introApp
    AddInductive.mkRecInfos.loopUTemplates stats allFields recursiveFields recInfos
      0 #[] #[] fun hypotheses calls => do
        let lctx ← getLCtx
        let minorTy := lctx.mkForall allFields <|
          lctx.mkForall hypotheses motiveApp
        let minorName := ctor.name.replacePrefix indTypeName .anonymous
        AddInductive.withUnannotatedLocalDecl minorName .default minorTy
            fun minor =>
          let next := recInfos.modify dIdx fun info =>
            { info with
              minors := info.minors.push minor
              ruleTemplates := info.ruleTemplates.push {
                ctor := ctor.name
                fields := allFields
                lctx := lctx
                recursiveCalls := calls
                targetTypeIdx := ownerIdx
                targetIndices := indices
                minor := minor } }
          k next
  change (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type process c).WF Q
  apply mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent (Q := Q)
    stats ctor.type tail
      (mkAppN (.const ctor.name stats.levels) stats.params)
      process c R Hstats hprefix hconsume hlit hctx htail Hsuffix htail₀ htail₀Ty
      htailType htailScope Hsuffix.parameterFVarsUp Hintro HintroType
  intro current Rargs terminal terminalTarget appliedTarget allFields
    recursiveFields fields positions args HterminalNonforall Hterminal
    HterminalType Hselections Hdecisions Hrecursive HfieldsRecent Hopening
    HfieldTargetDefEq _HterminalScope _HfieldParameterUp
    HintroApplied HintroAppliedType hchkFields hfieldCheck
  let HextArgs := HfieldsRecent.contextExtension
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  have hdidxDecl : dIdx < decl.types.length := by
    rw [← Hstats.types_size, ← hrecords]
    exact hidx
  have hdidxConst := Hstats.indConstAt hdidxDecl
  rcases Hnormal with ⟨Hnormal⟩
  have hdidxValid := Hnormal.validOfOpening Hopening Hparams
    hdidxConst HterminalNonforall
  rcases checkPositivityStep.isValidIndApp?_exists_of_valid
      hdidxValid hdidxConst with
    ⟨ownerIdx, hownerValid⟩
  let Happlication : ConstructorApplicationAt Rargs stats ctor
      terminal allFields terminalTarget := {
    ownerIdx := ownerIdx
    owner_valid := hownerValid
    terminal_type := HterminalType
    introTarget := appliedTarget
    intro := by simpa [mkAppN] using HintroApplied
    typing := HintroAppliedType }
  have htargetStats : Happlication.ownerIdx < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some Happlication.owner_valid).1
  have htarget : Happlication.ownerIdx < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : Happlication.ownerIdx < decl.types.length := by
    rw [← HstatsArgs.types_size]
    exact htargetStats
  let Hvalidated := HstatsArgs.validatedIndAppAt Hterminal
    Happlication.owner_valid htargetDecl
      (by simpa only [HfieldsRecent.venv_eq] using hlit) hctxArgs
  rcases HmotiveShapes.motiveBindingRecent Hbindings Horigins
      HfieldsRecent Happlication.ownerIdx htarget with ⟨Hbinding⟩
  have HmotiveEvidence := Htelescopes.telescope Happlication.ownerIdx
    htarget Rargs HextArgs Hbinding Hterminal HterminalType Hvalidated
  have HterminalWF : VExpr.WF Rargs.venv recLparams.length
      Rargs.mlctx.vlctx.toCtx terminalTarget := by
    rcases Happlication.terminal_type with ⟨u, Htyped⟩
    exact ⟨.sort u, Htyped⟩
  rcases Htelescopes.applications.applyAtMono Hbindings Horigins
      HmotiveShapes HextArgs Happlication.ownerIdx htarget Hterminal
      (.refl HterminalWF) Happlication.terminal_type
      Happlication.intro Happlication.typing Hvalidated with
    ⟨motiveTarget, Hmotive, HmotiveType⟩
  let indices : Array Expr := terminal.getAppArgs[stats.params.size:]
  have howner : AddInductive.getIIndices stats terminal =
      (Happlication.ownerIdx, indices) := by
    simp only [AddInductive.getIIndices, indices]
    rw [Happlication.owner_valid]
    rfl
  dsimp only [process]
  rw [howner]
  let finish := fun hypotheses calls => do
    let lctx ← getLCtx
    let motiveApp := Expr.app
      (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
      (mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
    let minorTy := lctx.mkForall allFields <|
      lctx.mkForall hypotheses motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    AddInductive.withUnannotatedLocalDecl minorName .default minorTy
        fun minor =>
      let next := recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleTemplates := info.ruleTemplates.push {
            ctor := ctor.name
            fields := allFields
            lctx := lctx
            recursiveCalls := calls
            targetTypeIdx := Happlication.ownerIdx
            targetIndices := indices
            minor := minor } }
      k next
  change (AddInductive.mkRecInfos.loopUTemplates stats allFields recursiveFields
    recInfos 0 #[] #[] finish current).WF Q
  let HbindingsArgs := Hbindings.mono HextArgs.contextLE
  let HoriginsArgs := Horigins.mono HextArgs.contextLE
  let HmotiveShapesArgs := HmotiveShapes.mono Hbindings HextArgs.contextLE
  let HtelescopesArgs := Htelescopes.mono HextArgs
  let producerScope : FVarId → Prop := fun fv =>
    fv ∈ HfieldsRecent.fvars ∨ fv ∈ ExprArrayFVarIds stats.params
  have hproducerUp : IsFVarUpSet producerScope Rargs.mlctx.vlctx := by
    dsimp only [producerScope]
    rw [Hopening.fvars_eq_bound
      HfieldsRecent.toFVarArrayAfter.toFVarArrayIn] at _HfieldParameterUp
    exact _HfieldParameterUp
  have hsharpUp : ∀ j : Nat, IsFVarUpSet
      (RecursorFieldPrefixScope stats.params HfieldsRecent.fvars
        recursiveFields[j]!) Rargs.mlctx.vlctx := fun j =>
    constructorFieldPrefixScopeUp HfieldsRecent Hparams hproducerUp
      recursiveFields[j]!
  have hfieldSupport :=
    (Hdecisions.levelParamsIn R.toBindingContextWF htailUniverses).2
  have hparamSupport := hparamUniverses.mono Hparams HextArgs.contextLE
  have hlparams : current.lparams = c.lparams := HextArgs.contextLE.lparams_eq
  have hfieldTypes : ∀ fv, fv ∈ HfieldsRecent.fvars → ∀ decl,
      current.lctx.find? fv = some decl →
        decl.type.levelParamsIn current.lparams = true := by
    intro fv hfv decl hfind
    have he : Expr.fvar fv ∈ allFields := by
      rw [HfieldsRecent.expressions]
      simpa using hfv
    obtain ⟨fv', index, name, type, bi, kind, heq, hfind', htype⟩ :=
      hfieldSupport _ he
    cases heq
    rw [hfind'] at hfind
    cases hfind
    rw [hlparams]
    exact htype
  have hproducerUniverses :
      Rargs.typeChecker.UniverseScope current.lparams producerScope := by
    refine Rargs.universeScope_of_types hproducerUp ?_
    rintro fv (hfv | hfv) decl hfind
    · exact hfieldTypes fv hfv decl hfind
    · exact hparamSupport fv hfv decl hfind
  have hsharpUniverses : ∀ j : Nat, Rargs.typeChecker.UniverseScope current.lparams
      (RecursorFieldPrefixScope stats.params HfieldsRecent.fvars
        recursiveFields[j]!) := by
    intro j
    refine Rargs.universeScope_of_types (hsharpUp j) ?_
    rintro fv (hfv | hfv) decl hfind
    · exact hfieldTypes fv (List.mem_of_mem_take hfv) decl hfind
    · exact hparamSupport fv hfv decl hfind
  have hfieldUniverses : ∀ j (hj : j < recursiveFields.size) fv,
      recursiveFields[j] = .fvar fv → ∀ decl,
        current.lctx.find? fv = some decl →
          decl.type.levelParamsIn current.lparams = true := by
    intro j hj fv hfv decl hfind
    have hallExpr : Expr.fvar fv ∈ allFields.toList := by
      apply Hselections.toSource.selectedSublist.subset
      rw [← hfv]
      exact Array.getElem_mem_toList hj
    rw [HfieldsRecent.expressions] at hallExpr
    exact hfieldTypes fv (by simpa using hallExpr) decl hfind
  apply mkRecInfos.loopUTemplates.resultTypingOfMotiveTelescopes (Q := Q)
    stats allFields recursiveFields recInfos finish Rargs producerScope HstatsArgs
      hconsume
      (by simpa only [HfieldsRecent.venv_eq] using hlit)
      hctxArgs
      (by
        intro j hj
        rcases Hselections.selectedFVars
            HfieldsRecent.toFVarArrayAfter.toFVarArrayIn Hrecursive
            j hj with ⟨fv, target, heq, Htr⟩
        refine ⟨fv, target, heq, Htr, Or.inl ?_⟩
        have hselectedExpr : Expr.fvar fv ∈ recursiveFields.toList := by
          rw [← heq]
          exact Array.getElem_mem_toList hj
        have hallExpr : Expr.fvar fv ∈ allFields.toList :=
          Hselections.toSource.selectedSublist.subset hselectedExpr
        rw [HfieldsRecent.expressions] at hallExpr
        simpa using hallExpr)
      (by
        intro hpos
        have hmem : recursiveFields[0] ∈ allFields.toList :=
          Hselections.toSource.selectedSublist.subset (Array.getElem_mem_toList hpos)
        have hbu : 0 < allFields.size := by
          have := List.length_pos_of_mem hmem
          simpa using this
        rw [← Rargs.check.lctx_eq, Rargs.check.wf.toList_eq,
          TypeChecker.MLCtx.decls_fvarId, List.reverse_reverse]
        exact hchkFields hbu)
      (fun j hj => ⟨recursiveFields[j],
        Hselections.toSource.selectedSublist.subset (Array.getElem_mem_toList hj), rfl⟩)
      (by
        intro fv hfv
        rcases hfv with hfield | hparam
        · have hmem := HfieldsRecent.members fv hfield
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem
        · have hp : fv ∈ Hparams.fvars := by
            rw [← Hparams.exprArrayFVarIds]
            exact hparam
          have hmem := HextArgs.contextLE (Hparams.members fv hp)
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem)
      hproducerUp
      (fun j => RecursorFieldPrefixScope stats.params HfieldsRecent.fvars
        recursiveFields[j]!)
      (by
        intro j hj fv hfv decl hfind
        have hbang : recursiveFields[j]! = .fvar fv := by
          rw [getElem!_pos recursiveFields j hj]
          exact hfv
        have hallExpr : Expr.fvar fv ∈ allFields.toList := by
          apply Hselections.toSource.selectedSublist.subset
          rw [← hfv]
          exact Array.getElem_mem_toList hj
        rw [HfieldsRecent.expressions] at hallExpr
        have hmem : fv ∈ HfieldsRecent.fvars := by simpa using hallExpr
        have hpos : HfieldsRecent.fvars.idxOf fv < HfieldsRecent.fvars.length :=
          List.idxOf_lt_length_of_mem hmem
        have hfind' : current.lctx.find? HfieldsRecent.fvars[HfieldsRecent.fvars.idxOf fv] =
            some decl := by
          rw [List.getElem_idxOf hpos]
          exact hfind
        rw [Hopening.fvars_eq_bound
          HfieldsRecent.toFVarArrayAfter.toFVarArrayIn] at _HfieldParameterUp
        have hscope := HfieldsRecent.fieldTypeScope _HfieldParameterUp _ hpos decl hfind'
        rw [hbang]
        exact hscope)
      (by
        intro j fv hfv
        rcases hfv with hfield | hparam
        · have hmem := HfieldsRecent.members fv (List.mem_of_mem_take hfield)
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem
        · have hp : fv ∈ Hparams.fvars := by
            rw [← Hparams.exprArrayFVarIds]
            exact hparam
          have hmem := HextArgs.contextLE (Hparams.members fv hp)
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem)
      hsharpUp
      hproducerUniverses hsharpUniverses hfieldUniverses
      HtelescopesArgs HbindingsArgs HoriginsArgs HmotiveShapesArgs hrecords
  intro outCtx Rout hypotheses calls HhypothesesRecent HhypothesisOrigins
    HhypothesisCallOrigins HhypothesisCallSemantics HhypothesisCallSharpSemantics
    hhypothesesSize hcallsSize
  exact constructorMinorClosureTyping stats indTypes indTypeName dIdx
    recInfos ctor tail sourceConstructors sourceIndex hsourceConstructor
    hsourceFamily k R Hsuffix Hstats hprefix htailScope hconsume hctx htail
    htailType htail₀ htail₀Ty Hbindings Horigins Hblueprints
    HblueprintSemantics HminorSources HminorSemantics HmajorTypes HmajorShapes
    HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams HnoAlias Horder
    Hroot hidx hsourceIdx horiginIndex Harities Hlater Hk Rargs
    HterminalNonforall Hterminal HterminalType Hselections Hdecisions
    HfieldsRecent Hopening HfieldTargetDefEq hproducerUp hfieldCheck
    hdidxValid hdidxDecl Happlication htarget Hvalidated Hbinding
    HmotiveEvidence Hmotive HmotiveType howner Rout hypotheses calls
    HhypothesesRecent HhypothesisOrigins HhypothesisCallOrigins
    HhypothesisCallSemantics HhypothesisCallSharpSemantics hhypothesesSize

/-- Refinement of the complete constructor list for one mutual
family.  Each iteration uses the checked constructor data for its
constructor and adds exactly one verified minor to the owning recursor row. -/
theorem resultTyping {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hconstructors : ctors = sourceConstructors.drop sourceIndex)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos
      Horigins.majorTypes c.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn c stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hparamUniverses : ParameterUniverseSupport c stats.params)
    (htailUniverses : ∀ ctor ∈ ctors, ∀ tail,
      ParameterPrefix stats 0 ctor.type tail →
        tail.levelParamsIn c.lparams = true)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hminorIndex : recInfos[dIdx]!.minors.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = Hsuffix.parameterDecls →
      ∀ ctor, ctor ∈ ctors →
      ∃ tail tailTarget introTarget,
        ParameterPrefix stats 0 ctor.type tail ∧
        Nonempty (ConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget ∧
        ∃ tailTarget₀, TrExprS Rcurrent.venv recLparams
          HsuffixCurrent.parameterDecls tail tailTarget₀ ∧
          Rcurrent.venv.IsType recLparams.length
            HsuffixCurrent.parameterDecls.toCtx tailTarget₀)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = Hsuffix.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoBinderTypes outCtx out) →
      RuleTemplatesMatch stats out HoriginsOut →
      TypedRuleTemplates Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      MinorsAndIndicesMatchSource stats indTypes HoriginsOut →
      TypedMinors Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c depth sourceIndex with
  | nil =>
      exact Hk recInfos R rfl Hsuffix rfl Hstats hctx Hbindings Horigins
        Hblueprints HblueprintSemantics HminorSources HminorSemantics rfl (by simp)
        (by intros; rfl)
        HmajorTypes HmajorShapes
        HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams HnoAlias
        Horder Harities Hroot
  | cons ctor ctors ih =>
      have hsourceConstructor :
          sourceConstructors[sourceIndex]? = some ctor := by
        have hhead := congrArg (fun xs => xs[0]?) hconstructors
        simpa using hhead.symm
      have htailConstructors :
          ctors = sourceConstructors.drop (sourceIndex + 1) := by
        have htail := congrArg List.tail hconstructors
        simpa [List.tail_drop] using htail
      have horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex := by
        rw [(Horigins.minors dIdx hidx).size_eq]
        exact hminorIndex
      rcases Hseed R rfl Hsuffix rfl ctor (by simp) with
        ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailScope, Htail,
          HtailType, Hintro, HintroType, tailTarget₀, Htail₀, Htail₀Ty⟩
      rw [AddInductive.mkRecInfos.loopCtors]
      refine oneConstructorTyping (Q := Q) stats indTypes indTypeName dIdx recInfos
        ctor tail sourceConstructors sourceIndex hsourceConstructor hsourceFamily
        (fun next => AddInductive.mkRecInfos.loopCtors stats indTypeName
          dIdx next ctors k)
        R Hsuffix Hstats Hprefix HtailScope hparamUniverses
        (htailUniverses ctor (by simp) tail Hprefix)
        hconsume hlit hctx Htail
        HtailType Htail₀ Htail₀Ty Hintro HintroType Hbindings Horigins Hblueprints
        HblueprintSemantics HminorSources
        HminorSemantics HmajorTypes
        HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows
        Hparams HnoAlias Horder (BindingContextLE.refl c) hidx hsourceIdx
        horiginIndex Harities Hlater hrecords Hnormal ?_
      intro nextCtx nextDepth next Rnext henvNext HsuffixNext
        hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
        HblueprintsNext HblueprintSemanticsNext HminorSourcesNext HminorSemanticsNext
        hsizeNext hcountNext hotherNext
        HmajorTypesNext HmajorShapesNext
        HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
        HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
      refine ih next (sourceIndex + 1) htailConstructors Rnext HsuffixNext
        HstatsNext (by simpa only [henvNext] using hlit) hctxNext HbindingsNext
        HoriginsNext HblueprintsNext HblueprintSemanticsNext HminorSourcesNext
        HminorSemanticsNext
        HmajorTypesNext
        HmajorShapesNext HmotiveTypesNext
        HmotiveShapesNext HtelescopesNext HindexRowsNext HparamsNext
        HnoAliasNext HorderNext (Hroot.trans HrootNext)
        (hparamUniverses.mono Hparams HrootNext)
        (fun ctor' hctor' tail' Hprefix' => by
          rw [HrootNext.lparams_eq]
          exact htailUniverses ctor' (by simp [hctor']) tail' Hprefix')
        ?_ ?_ HaritiesNext ?_ ?_ ?_ ?_
      · simpa [hsizeNext] using hidx
      · rw [hcountNext, hminorIndex]
      · intro i hdi hiNext
        rw [hotherNext i (by simpa [hsizeNext] using hiNext)
          (Nat.ne_of_lt hdi)]
        exact Hlater i hdi (by simpa [hsizeNext] using hiNext)
      · exact hsizeNext.trans hrecords
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent nextCtor hnextCtor
        apply Hseed Rcurrent (henvCurrent.trans henvNext) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsNext) nextCtor
        simp [hnextCtor]
      · intro outCtx outDepth out Rout henvOut HsuffixOut
          hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
          HblueprintsOut HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut
          houtSize houtCount houtOther
          HmajorTypesOut HmajorShapesOut
          HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
          HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size :=
          houtSize.trans hsizeNext
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount, hcountNext]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [hsizeNext] using hi) hine]
          exact hotherNext i hi hine
        exact Hk out Rout (henvOut.trans henvNext) HsuffixOut
          (hparameterDeclsOut.trans hparameterDeclsNext) HstatsOut hctxOut
          HbindingsOut HoriginsOut HblueprintsOut HblueprintSemanticsOut HminorSourcesOut
          HminorSemanticsOut
          houtSize' houtCount' houtOther'
          HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
          HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
          HaritiesOut HrootOut

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

/-- Refinement of the complete minor pass (`loopInd2`).  The processed
prefix has its constructor/minor cardinalities, the unprocessed suffix
is empty, and the checked data of every constructor is used at its
mutual-family owner. -/
theorem resultTyping {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (HsuffixCtx : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hblueprints : RuleTemplatesMatch stats recInfos Horigins)
    (HblueprintSemantics : TypedRuleTemplates R decl stats
      recInfos elimLevel HsuffixCtx.parameterDecls Horigins)
    (HminorSources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    (HminorSemantics : TypedMinors R Horigins
      HsuffixCtx.parameterDecls)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos
      Horigins.majorTypes c.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn c stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hparamUniverses : ParameterUniverseSupport c stats.params)
    (htailUniverses : ∀ familyIdx (hfamily : familyIdx < indTypes.size),
      ∀ ctor ∈ indTypes[familyIdx].ctors, ∀ tail,
        ParameterPrefix stats 0 ctor.type tail →
          tail.levelParamsIn c.lparams = true)
    (hsize : recInfos.size = indTypes.size)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (HemptySuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = HsuffixCtx.parameterDecls →
      ∀ familyIdx, (hfamily : familyIdx < indTypes.size) →
      ∀ ctor, ctor ∈ indTypes[familyIdx].ctors →
      ∃ tail tailTarget introTarget,
        ParameterPrefix stats 0 ctor.type tail ∧
        Nonempty
          (ConstructorOwnerNormalForm stats familyIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget ∧
        ∃ tailTarget₀, TrExprS Rcurrent.venv recLparams
          HsuffixCurrent.parameterDecls tail tailTarget₀ ∧
          Rcurrent.venv.IsType recLparams.length
            HsuffixCurrent.parameterDecls.toCtx tailTarget₀)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = HsuffixCtx.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoBinderTypes outCtx out) →
      RuleTemplatesMatch stats out HoriginsOut →
      TypedRuleTemplates Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      MinorsAndIndicesMatchSource stats indTypes HoriginsOut →
      TypedMinors Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hfamily : dIdx < indTypes.size
  · rw [dif_pos hfamily]
    refine mkRecInfos.loopCtors.resultTyping (Q := Q) stats indTypes
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      indTypes[dIdx].ctors 0 rfl
      (by simp [getElem!_pos indTypes dIdx hfamily])
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      R HsuffixCtx Hstats hconsume hlit hctx Hbindings
      Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics
      HmajorTypes HmajorShapes
      HmotiveTypes HmotiveShapes
      Htelescopes HindexRows Hparams HnoAlias Horder (BindingContextLE.refl c)
      hparamUniverses (htailUniverses dIdx hfamily)
      (by simpa [hsize] using hfamily)
      hfamily
      (by
        exact HemptySuffix dIdx (Nat.le_refl _) (by
          simpa [hsize] using hfamily))
      Harities (fun i hdi hi => HemptySuffix i (by omega) hi) hrecords ?_ ?_
    · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent ctor hctor
      exact Hseed Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent dIdx hfamily ctor hctor
    · intro outCtx outDepth out Rout henvOut HsuffixOut
        hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
        HblueprintsOut HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut
        houtSize houtCount houtOther
        HmajorTypesOut HmajorShapesOut
        HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
        HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
      refine resultTyping (root := root) (Q := Q) stats indTypes
        (dIdx + 1) out k Rout HsuffixOut HstatsOut hconsume
        (by simpa only [henvOut] using hlit)
        hctxOut HbindingsOut HoriginsOut HblueprintsOut
        HblueprintSemanticsOut HminorSourcesOut
        HminorSemanticsOut HmajorTypesOut
        HmajorShapesOut HmotiveTypesOut HmotiveShapesOut HtelescopesOut
        HindexRowsOut HparamsOut HnoAliasOut HorderOut (Hroot.trans HrootOut)
        (hparamUniverses.mono Hparams HrootOut)
        (fun familyIdx hfamilyIdx ctor hctor tail Hprefix => by
          rw [HrootOut.lparams_eq]
          exact htailUniverses familyIdx hfamilyIdx ctor hctor tail Hprefix)
        ?_ ?_
        HaritiesOut
        ?_ ?_ ?_ ?_
      · exact houtSize.trans hsize
      · exact houtSize.trans hrecords
      · intro i hiDone hiOut
        by_cases hieq : i = dIdx
        · subst i
          rw [houtCount, HemptySuffix dIdx (Nat.le_refl _) (by
            simpa [houtSize] using hiOut)]
          simp [hfamily]
        · rw [houtOther i (by simpa [houtSize] using hiOut)
            (Ne.symm hieq)]
          exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
      · intro i hiNext hiOut
        have hine : dIdx ≠ i := by omega
        rw [houtOther i (by simpa [houtSize] using hiOut) hine]
        exact HemptySuffix i (by omega) (by simpa [houtSize] using hiOut)
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent familyIdx hfamilyIdx ctor hctor
        exact Hseed Rcurrent (henvCurrent.trans henvOut) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsOut) familyIdx
          hfamilyIdx ctor hctor
      · intro finalCtx finalDepth final Rfinal henvFinal HsuffixFinal
          hparameterDeclsFinal HstatsFinal hctxFinal HbindingsFinal
          HoriginsFinal HblueprintsFinal HblueprintSemanticsFinal
          HminorSourcesFinal HminorSemanticsFinal
          hfinalSize hfinalCounts HmajorTypesFinal
          HmajorShapesFinal HmotiveTypesFinal HmotiveShapesFinal
          HtelescopesFinal HindexRowsFinal HparamsFinal HnoAliasFinal
          HorderFinal HaritiesFinal HrootFinal
        exact Hk final Rfinal (henvFinal.trans henvOut) HsuffixFinal
          (hparameterDeclsFinal.trans hparameterDeclsOut) HstatsFinal
          hctxFinal HbindingsFinal HoriginsFinal HblueprintsFinal
          HblueprintSemanticsFinal HminorSourcesFinal
          HminorSemanticsFinal hfinalSize hfinalCounts
          HmajorTypesFinal HmajorShapesFinal HmotiveTypesFinal
          HmotiveShapesFinal HtelescopesFinal HindexRowsFinal HparamsFinal
          HnoAliasFinal HorderFinal HaritiesFinal HrootFinal
  · rw [dif_neg hfamily]
    exact Hk recInfos R rfl HsuffixCtx rfl Hstats hctx Hbindings Horigins
      Hblueprints HblueprintSemantics HminorSources HminorSemantics hsize
      (fun i hi => Hprefix i (by omega) hi) HmajorTypes
      HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams
      HnoAlias Horder Harities Hroot
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

end VerifyInductive
end Lean4Lean
