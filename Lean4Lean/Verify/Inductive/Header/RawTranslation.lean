import Lean4Lean.Verify.Inductive.Header.Telescope

/-!
# Raw header translations

The first step of the header phase (section 3.2 of the design notes): each
successful `checkClosedType` of a family type yields a raw source translation of the header
(`ClosedHeaderCheck`, `TrSourceConstRaw`), without `VConstVal.WF`. The mutual-header loop
accumulates these in source order (`RawHeaderTranslations`,
`checkInductiveTypes.loopInd.stepPrefix.accumulatesRawHeaders`), before any declaration
skeleton or constructor translation exists.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The abstract payload obtained directly from one successful closed header
check.  Its type translation is exact, but it deliberately does not claim
`VConstVal.WF`: header formation is established only after the executable
telescope traversal has checked the parameter/index telescope and result
sort. -/
structure ClosedHeaderCheck
    (Hc : ContextWF c) (name : Name) (type checkedType : Expr) where
  target : VConstVal
  runtimeTarget : VExpr
  checkedTarget : VExpr
  typing : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
    type checkedType runtimeTarget checkedTarget
  source : TrSourceConstRaw Hc.venv c.lparams name type target

/-- The declaration-facing part of a checked source header.  Unlike
`ClosedHeaderCheck`, this payload no longer mentions the
executable result of `checkClosedType`, so payloads from successive mutual
headers can be retained in one ordered accumulator even though those checks
run in different local contexts. -/
structure RawHeaderTranslation (env : VEnv) (Us : List Name)
    (source : InductiveType) where
  target : VConstVal
  translation : TrSourceConstRaw env Us source.name source.type target

/-- Ordered abstract payloads recovered from a prefix of the executable
mutual-header traversal.  This is intentionally earlier than a
`VInductDeclSkeleton`: constructors have not been translated yet, and the
header telescope traversal has not yet supplied semantic arities. -/
structure RawHeaderTranslations (env : VEnv) (Us : List Name)
    (sources : List InductiveType) where
  targets : List VConstVal
  translations : List.Forall₂
    (fun source target =>
      TrSourceConstRaw env Us source.name source.type target)
    sources targets

namespace RawHeaderTranslations

/-- The empty executable header prefix has an empty abstract payload. -/
def empty (env : VEnv) (Us : List Name) :
    RawHeaderTranslations env Us [] where
  targets := []
  translations := .nil

/-- Retain one newly checked source header at the end of the ordered prefix. -/
def snoc (H : RawHeaderTranslations env Us sources)
    (source : InductiveType) (payload : RawHeaderTranslation env Us source) :
    RawHeaderTranslations env Us (sources ++ [source]) where
  targets := H.targets ++ [payload.target]
  translations := List.Forall₂.append'
    H.translations (.cons payload.translation .nil)

@[simp] theorem empty_targets : (empty env Us).targets = [] := rfl

@[simp] theorem snoc_targets
    (H : RawHeaderTranslations env Us sources)
    (payload : RawHeaderTranslation env Us source) :
    (H.snoc source payload).targets = H.targets ++ [payload.target] := rfl

end RawHeaderTranslations

/-- Exact loop-indexed view of the accumulated mutual-header payloads. -/
structure CheckedSourceHeaderTraversal (env : VEnv) (Us : List Name)
    (indTypes : Array InductiveType) (dIdx : Nat) where
  accumulator : RawHeaderTranslations env Us
    (indTypes.toList.take dIdx)

namespace CheckedSourceHeaderTraversal

def empty (env : VEnv) (Us : List Name) (indTypes : Array InductiveType) :
    CheckedSourceHeaderTraversal env Us indTypes 0 where
  accumulator := RawHeaderTranslations.empty env Us

end CheckedSourceHeaderTraversal

namespace ClosedHeaderCheck

/-- Forget the context-sensitive typing of the checked type, keeping the
raw source translation. -/
def payload
    {c : AddInductive.Context} {source : InductiveType} {checkedType : Expr}
    (Hc : ContextWF c)
    (H : ClosedHeaderCheck Hc source.name source.type checkedType) :
    RawHeaderTranslation Hc.venv c.lparams source where
  target := H.target
  translation := H.source

end ClosedHeaderCheck

/-- A successful `checkClosedType` constructs its abstract header payload;
no caller-selected declaration skeleton is needed at this boundary.  This
existential form separates checking the headers from the later translation
of the constructors. -/
theorem checkClosedType.rawSourceTranslationWF (Hc : ContextWF c) :
    (AddInductive.checkClosedType name type c).WF fun checkedType =>
      Nonempty (ClosedHeaderCheck Hc name type checkedType) := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    (monadLift (TypeChecker.checkType type) : AddInductive.M Expr)
      { c with checkLCtx := {} }).WF _
  have Hclosed : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ Hresult
    exact checkNoMVarNoFVar.closed Hresult
  -- The closed check runs in the empty checker context, where it produces
  -- the closed translation of the header directly.
  let Hc0 := Hc.withCheckLCtx {} Hc.baseNil
  exact Hclosed.bind fun _ hclosed =>
    (checkTypeInContext.checkingWF Hc0
      (hclosed.mono fun _ h => False.elim h)).mono
      fun checkedType Hchecked => by
    rcases Hchecked with ⟨typeTarget, checkedTarget₀, HtypingClosed⟩
    change TrTyping Hc.venv c.lparams [] type checkedType typeTarget checkedTarget₀
      at HtypingClosed
    obtain ⟨runtimeTarget, hruntime⟩ :=
      Hc0.check.embed.trExprS Hc.checking.tr.wf HtypingClosed.2.1
    obtain ⟨checkedTarget, Htyping⟩ :=
      Hc0.check.embed.trTyping Hc.checking.tr.wf hruntime HtypingClosed
    let target : VConstVal := {
      uvars := c.lparams.length
      name := name
      type := typeTarget }
    exact ⟨{
      target := target
      runtimeTarget := runtimeTarget
      checkedTarget := checkedTarget
      typing := Htyping
      source := {
        uvars := rfl
        name := rfl
        type := HtypingClosed.2.1 } }⟩

namespace checkInductiveTypes.loopInd

/-- One executable mutual-header iteration extends an independently built,
ordered abstract-header accumulator.  The continuation also receives the
full context-sensitive typing needed by `loopType`; only the stored
accumulator forgets it.  No constructor translation or
caller-selected declaration skeleton is assumed at this boundary. -/
theorem stepPrefix.accumulatesRawHeaders
    {sources : List InductiveType}
    {c : AddInductive.Context} {nparams dIdx : Nat}
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {k : AddInductive.InductiveStats → AddInductive.M α}
    {Q : α → Prop}
    (Hc : ContextWF c)
    (Hprefix : RawHeaderTranslations Hc.venv c.lparams sources)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType,
      (Hchecked : ClosedHeaderCheck Hc indTypes[dIdx].name
        indTypes[dIdx].type checkedType) →
      RawHeaderTranslations Hc.venv c.lparams
        (sources ++ [indTypes[dIdx]]) →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
          normalized Hchecked.runtimeTarget →
        TrExpr Hc.venv c.lparams [] normalized Hchecked.target.type →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k) (headerCheckContext c stats)).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_pos hidx]
  change (AddInductive.checkClosedType indTypes[dIdx].name indTypes[dIdx].type c >>=
    fun _ => ((do
      let normalized ← AddInductive.withCheckLCtx {}
        (TypeChecker.whnf indTypes[dIdx].type)
      AddInductive.withCheckLCtx
        (← AddInductive.paramCheckLCtx stats stats.params.size) do
      AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other
              "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.rawSourceTranslationWF Hc).bind
    fun checkedType hchecked => by
      rcases hchecked with ⟨Hchecked⟩
      exact (whnfInContext.dualWF
        (Hc.withCheckLCtx {} Hc.baseNil)
        Hchecked.typing.2.1 Hchecked.source.type).bind
        fun normalized ⟨⟨hbelow, hnormalized⟩, _, hnormalized₀⟩ =>
          AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => by
            subst hL
            exact Hloop checkedType Hchecked
              (Hprefix.snoc indTypes[dIdx] (Hchecked.payload Hc))
              normalized hbelow hnormalized hnormalized₀

end checkInductiveTypes.loopInd


end VerifyInductive
end Lean4Lean
