import Lean4Lean.Verify.Inductive.Header.CheckingScope

/-!
# The cached-parameter suffix of an inductive-checker frame

`ParameterContextSuffix S stats depth` splits the main local context of a frame
`S : ContextSemantics c Us` into the ambient declarations opened after the parameter phase and
the cached parameter declarations below them. Every lemma here is stated over the shared frame
record, so the same suffix theory serves the header phase (`ContextWF`, at the declaration's
universe parameters) and the recursor phase (`RecursorContextWF`, at the recursor's universe
parameters); the two frame-specific views are `ParameterContextSuffix.headerCheck` and
`ParameterContextSuffix.recursorHeaderCheck`. `ReusedParameterScope` locates one cached
parameter in that suffix, as later mutual headers and the recursor construction need when they
rerun the header steps.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

namespace checkInductiveTypes.loopType

theorem CachedParameterDecl.forall₂_fvars
    (H : List.Forall₂ CachedParameterDecl ps decls) :
    VLCtx.fvars decls = ps.map (·.fvarId!) := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨fv, deps, ty, rfl, rfl⟩ := h
    simp [VLCtx.fvars_cons_some, ih, Expr.fvarId!]

theorem CachedParameterDecl.forall₂_drop :
    ∀ (n : Nat) {ps : List Expr} {decls : VLCtx},
      List.Forall₂ CachedParameterDecl ps decls →
      List.Forall₂ CachedParameterDecl (ps.drop n) (decls.drop n)
  | 0, _, _, H => by simpa using H
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ H => by simpa using CachedParameterDecl.forall₂_drop n H

end checkInductiveTypes.loopType

open checkInductiveTypes.loopType

def ParameterContextSuffix.empty
    (S : ContextSemantics c Us) (hctx : S.mlctx.vlctx = [])
    (hparams : stats.params = #[]) :
    ParameterContextSuffix S stats 0 where
  ambientDecls := []
  parameterDecls := []
  context := by simpa using hctx
  prefixLength := rfl
  cached := by simp [hparams]
  suffixParams := by simp [hparams]
  sources := .nil

/-- The first-header parameter branch extends the cached suffix itself.  The
empty-prefix premise records that parameters are all introduced before any
index binder. -/
def ParameterContextSuffix.push
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats 0)
    (hprefix : H.ambientDecls = [])
    (htr : TrExprS S.venv Us S.mlctx.vlctx ty ty')
    (hty : S.venv.IsType Us.length S.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS S.venv Us S.chk.vlctx ty ty₀)
    (hty₀ : S.venv.IsType Us.length S.chk.vlctx.toCtx ty₀) :
    ParameterContextSuffix
      (S.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      0 := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := []
    parameterDecls := entry :: H.parameterDecls
    context := ?_
    prefixLength := rfl
    cached := ?_
    suffixParams := ?_
    sources := ?_ }
  · have hcontext := H.context
    rw [hprefix] at hcontext
    change entry :: S.mlctx.vlctx = [] ++ entry :: H.parameterDecls
    simp only [List.nil_append]
    simpa using congrArg (entry :: ·) hcontext
  · simp only [Array.toList_push, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    exact .cons ⟨⟨c.ngen.curr⟩, ty.fvarsList, ty', rfl, rfl⟩
      H.cached
  · let S' := S.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀
    let W : VLCtx.FVLift H.parameterDecls
        (entry :: H.parameterDecls) 0 1 0 :=
      .skip_fvar _ _ .refl
    have hscope : S.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    have hnarrowWF : VLCtx.WF S'.venv Us.length
        (entry :: H.parameterDecls) := by
      change VLCtx.WF S.venv Us.length
        (entry :: H.parameterDecls)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hscope] using S.mlctx_wf.tr.wf
      · intro fv deps heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨by simpa [hscope] using S.current_not_mem,
          by simpa [hscope] using htr.fvarsList⟩
      · change S.venv.IsType Us.length
          H.parameterDecls.toCtx ty'
        simpa [hscope] using hty
    have hold : List.Forall₂
        (TrExprS S'.venv Us (entry :: H.parameterDecls))
        stats.params.toList
        ((cachedParamVars stats.params.size 0).map
          fun e => e.liftN 1 0) := by
      have weakAll : ∀ {as bs},
          List.Forall₂
              (TrExprS S.venv Us H.parameterDecls) as bs →
            List.Forall₂
              (TrExprS S'.venv Us (entry :: H.parameterDecls))
              as (bs.map fun e => e.liftN 1 0) := by
        intro as bs hp
        induction hp with
        | nil => exact .nil
        | cons h _ ih =>
          exact .cons
            (h.weakFV S.checking.tr.wf.orderedStrong W hnarrowWF) ih
      exact weakAll H.suffixParams
    have hnew : TrExprS S'.venv Us
        (entry :: H.parameterDecls)
        (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
      apply TrExprS.fvar (A := ty'.lift)
      simp [entry, VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type]
    simpa [Array.toList_push, cachedParamVars_succ] using
      List.Forall₂.append' hold
        (.cons hnew .nil)
  · have hscope : S.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    change SourceTelescope S.venv Us
      (entry :: H.parameterDecls)
    exact .cons H.sources name bi ty (by simpa [hscope] using htr)

/-- Index binders extend only the ambient prefix and preserve the exact
cached-parameter suffix. -/
def ParameterContextSuffix.withIndex
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth)
    (htr : TrExprS S.venv Us S.mlctx.vlctx ty ty')
    (hty : S.venv.IsType Us.length S.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS S.venv Us S.chk.vlctx ty ty₀)
    (hty₀ : S.venv.IsType Us.length S.chk.vlctx.toCtx ty₀) :
    ParameterContextSuffix
      (S.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := ?_
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    suffixParams := H.suffixParams
    sources := H.sources }
  change entry :: S.mlctx.vlctx =
    (entry :: H.ambientDecls) ++ H.parameterDecls
  simp only [List.cons_append]
  rw [H.context]

/-- A local added by the recursor construction extends only the ambient prefix. The
cached parameter suffix and its translations are unchanged. -/
def ParameterContextSuffix.withAmbient
    {c : AddInductive.Context}
    {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth)
    (htr : TrExprS S.venv Us S.mlctx.vlctx ty ty')
    (hty : S.venv.IsType Us.length S.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix (S.withLocalDecl (name := name) (bi := bi) htr hty)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  exact {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := by
      change entry :: S.mlctx.vlctx =
        (entry :: H.ambientDecls) ++ H.parameterDecls
      simpa only [List.cons_append] using congrArg (entry :: ·) H.context
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    suffixParams := H.suffixParams
    sources := H.sources }

theorem ParameterContextSuffix.parameterDecls_length
    (H : ParameterContextSuffix S stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := List.Forall₂.length_eq
    H.cached
  simpa using hlength.symm

/-- Locate executable parameter `i` in the reverse-ordered local-context
suffix. -/
theorem ParameterContextSuffix.parameterAt
    (H : ParameterContextSuffix S stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := by
    exact hj
  have hcached := List.forall₂_getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change CachedParameterDecl stats.params[stats.params.size - 1 - j]
    H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

/-- Split the cached-parameter suffix at executable array index `i`.  Entries
in `newer` are precisely the cached declarations introduced after parameter
`i`; `older` contains those introduced before it. -/
theorem ParameterContextSuffix.splitAt
    (H : ParameterContextSuffix S stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      CachedParameterDecl stats.params[i] entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

/-- Expose the exact `FVLift` that removes the ambient declarations and the
cached parameters newer than executable parameter `i`, leaving that
parameter as the head of the retained suffix. -/
theorem ParameterContextSuffix.fvLiftAt
    (H : ParameterContextSuffix S stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      S.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        S.mlctx.vlctx
        0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : S.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact S.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older)
      hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, rfl,
    hcontext, hparam, hlift⟩

theorem _root_.Lean4Lean.TypeChecker.MLCtx.fvarList_eq (m : TypeChecker.MLCtx) :
    m.fvarList = m.vlctx.fvars.reverse := by
  induction m with
  | nil => rfl
  | vlam id _ _ _ _ c ih =>
    simp [TypeChecker.MLCtx.fvarList, ih, TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]
  | vlet id _ _ _ _ _ c ih =>
    simp [TypeChecker.MLCtx.fvarList, ih, TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]

theorem ParameterContextSuffix.mlctx_length
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) :
    S.mlctx.length = depth + stats.params.size := by
  rw [← TypeChecker.MLCtx.vlctx_length, H.context, List.length_append,
    H.prefixLength, H.parameterDecls_length]

/-- The first `k` parameters are the `k` oldest declarations of the main
context: the bottom of the context that drops all but them. -/
theorem ParameterContextSuffix.bottom
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) (k : Nat)
    (hk : k ≤ stats.params.size) :
    (S.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) ∧
    paramCheckFVars stats k =
      (S.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).fvarList := by
  have hvl : (S.mlctx.dropN (depth + (stats.params.size - k))
      (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) := by
    rw [S.onlyLams.vlctx_dropN, H.context, List.drop_append, H.prefixLength]
    rw [List.drop_eq_nil_of_le (by rw [H.prefixLength]; omega)]
    simp
  refine ⟨hvl, ?_⟩
  rw [TypeChecker.MLCtx.fvarList_eq, hvl]
  have hcached := H.cached
  have hdrop : List.Forall₂ CachedParameterDecl
      (stats.params.toList.reverse.drop (stats.params.size - k))
      (H.parameterDecls.drop (stats.params.size - k)) :=
    CachedParameterDecl.forall₂_drop _ hcached
  rw [CachedParameterDecl.forall₂_fvars hdrop, ← List.map_reverse]
  unfold paramCheckFVars
  congr 1
  have hlen : stats.params.toList.length = stats.params.size := by simp
  rw [List.drop_reverse]
  simp only [List.reverse_reverse]
  congr 1
  omega

theorem ParameterContextSuffix.depth_le
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) :
    depth ≤ S.mlctx.length := by
  rw [H.mlctx_length]; omega

theorem ParameterContextSuffix.headerFVars
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) :
    paramCheckFVars stats stats.params.size =
      (S.mlctx.dropN depth H.depth_le).fvarList := by
  have h := (H.bottom stats.params.size (Nat.le_refl _)).2
  simp only [Nat.sub_self, Nat.add_zero] at h
  exact h

theorem ParameterContextSuffix.headerVLCtx
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) :
    (S.mlctx.dropN depth H.depth_le).vlctx = H.parameterDecls := by
  have h := (H.bottom stats.params.size (Nat.le_refl _)).1
  simp only [Nat.sub_self, Nat.add_zero, List.drop_zero] at h
  exact h

/-- The cached parameter suffix is well formed on its own, without the ambient
declarations above it in the recursor context. -/
theorem ParameterContextSuffix.parameterWF
    {c : AddInductive.Context} {Us : List Name}
    {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix S stats depth) :
    VLCtx.WF S.venv Us.length H.parameterDecls := by
  have dropPrefix : ∀ (added suffix : VLCtx),
      VLCtx.WF S.venv Us.length (added ++ suffix) →
        VLCtx.WF S.venv Us.length suffix := by
    intro added
    induction added with
    | nil => intro suffix Hwf; simpa using Hwf
    | cons decl tail ih =>
      intro suffix Hwf
      exact ih suffix Hwf.1
  have Hwf := S.mlctx_wf.tr.wf
  rw [H.context] at Hwf
  exact dropPrefix H.ambientDecls H.parameterDecls Hwf

/-- The checker frame of a header or recursor index telescope: the checking context holds
exactly the cached parameters, which are the bottom of the main context. -/
abbrev ParameterContextSuffix.headerSemantics
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth) :
    ContextSemantics (headerCheckContext c stats) Us :=
  S.paramCheck stats stats.params.size depth H.depth_le H.headerFVars

theorem ParameterContextSuffix.headerCheck_chk_vlctx
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth) :
    H.headerSemantics.chk.vlctx = H.parameterDecls := H.headerVLCtx

/-- The same suffix, over the header checker frame. -/
def ParameterContextSuffix.toHeaderCheck
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth) :
    ParameterContextSuffix H.headerSemantics stats depth := { H with }

/-- In the header checker frame the parameter declarations are aligned with the checker
context. -/
theorem ParameterContextSuffix.headerCheck_paramAligned
    {c : AddInductive.Context} {Us : List Name} {S : ContextSemantics c Us}
    (H : ParameterContextSuffix S stats depth) :
    VLCtx.IsDefEq S.venv Us.length H.parameterDecls H.headerSemantics.chk.vlctx := by
  rw [H.headerCheck_chk_vlctx]
  exact .refl S.checking.tr.wf H.parameterWF

/-- The header checker frame of a header-phase suffix, as a `ContextWF`. -/
abbrev ParameterContextSuffix.headerCheck {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc.toSemantics stats depth) :
    ContextWF (headerCheckContext c stats) :=
  .ofSemantics H.headerSemantics Hc.typeCheckerLParams_eq

/-- The checker frame of a recursor index telescope, as a `RecursorContextWF`. -/
abbrev ParameterContextSuffix.recursorHeaderCheck {R : RecursorContextWF c recLparams}
    (H : ParameterContextSuffix R.toSemantics stats depth) :
    RecursorContextWF (headerCheckContext c stats) recLparams :=
  .ofSemantics H.headerSemantics R.typeCheckerLParams_eq R.lparams_origin

/-- Concrete scope of a later header immediately before processing cached
parameter `i`.
Only parameters already processed by this later header may occur; ambient
indices and the current-or-future cached parameters are excluded. -/
structure ReusedParameterScope
    (Hsuffix : ParameterContextSuffix S stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : S.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    S.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem ReusedParameterScope.olderLength
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size) :
    H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem ReusedParameterScope.older_eq_nil
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

/-- After the final cached parameter is processed, the accumulated
scope is exactly the complete cached-parameter suffix. -/
theorem ReusedParameterScope.scope
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

/-- Consecutive cached-parameter scopes agree on the processed suffix. -/
theorem ReusedParameterScope.nextOlder
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {e next : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (Hnext : ReusedParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

theorem ReusedParameterScope.openedFVars
    (H : ReusedParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem ReusedParameterScope.openedUpSet
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {body : Expr}
    (H : ReusedParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      S.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older) H.added
    (by simpa [H.context] using S.mlctx_wf.tr.wf)

/-- Substitution of the current cached parameter, followed by an executable
normalization step, cannot introduce dependencies outside the newly processed
parameter scope. -/
theorem ReusedParameterScope.unannotatedFVars
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {body normalized : Expr}
    (H : ReusedParameterScope Hsuffix i body)
    (hbelow : FVarsBelow S.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

theorem ReusedParameterScope.olderDrop
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e) (hi : i < stats.params.size) :
    Hsuffix.parameterDecls.drop (stats.params.size - i) = H.older ∧
    Hsuffix.parameterDecls.drop (stats.params.size - (i + 1)) =
      (some (H.fv, H.deps), .vlam H.paramType) :: H.older := by
  rw [H.parameterDecls]
  have hn := H.newerLength
  constructor
  · rw [show stats.params.size - i = H.newer.length + 1 by omega, List.drop_append]
    simp
  · rw [show stats.params.size - (i + 1) = H.newer.length by omega, List.drop_append]
    simp

/-- The checker contexts of the cached-parameter step: the parameters before
`i`, and those up to and including `i`, together with the declared type of
parameter `i` translated among the earlier parameters. -/
theorem ReusedParameterScope.scopedTyping
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e) (hi : i < stats.params.size) :
    (S.mlctx.dropN (depth + (stats.params.size - i))
        (by rw [Hsuffix.mlctx_length]; omega)).vlctx = H.older ∧
    (S.mlctx.dropN (depth + (stats.params.size - (i + 1)))
        (by rw [Hsuffix.mlctx_length]; omega)).vlctx =
      (some (H.fv, H.deps), .vlam H.paramType) :: H.older ∧
    ∃ paramTy, (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy) ∧
      TrExprS S.venv Us H.older paramTy H.paramType ∧
      S.venv.IsType Us.length H.older.toCtx H.paramType := by
  obtain ⟨hd₀, hd₁⟩ := H.olderDrop hi
  have hb₀ := (Hsuffix.bottom i (by omega)).1
  have hb₁ := (Hsuffix.bottom (i + 1) (by omega)).1
  rw [hd₀] at hb₀
  rw [hd₁] at hb₁
  refine ⟨hb₀, hb₁, ?_⟩
  have hj : depth + (stats.params.size - (i + 1)) ≤ S.mlctx.length := by
    rw [Hsuffix.mlctx_length]; omega
  have hmwf := S.mlctx_wf.dropN _ hj
  have hmem : H.fv ∈ (S.mlctx.dropN _ hj).vlctx.fvars := by
    rw [hb₁]; simp [VLCtx.fvars_cons_some]
  have hfind := S.onlyLams.dropN_find?_eq S.mlctx_wf _ hj hmem
  have honly := S.onlyLams.dropN _ hj
  generalize S.mlctx.dropN _ hj = m at hb₁ hmwf hfind honly
  cases m with
  | nil => simp at hb₁
  | vlet => exact honly.vlet_false.elim
  | vlam id name ty ty' bi tail =>
    simp only [TypeChecker.MLCtx.vlctx, List.cons.injEq, Prod.mk.injEq,
      Option.some.injEq] at hb₁
    obtain ⟨⟨⟨rfl, -⟩, hty'⟩, htail⟩ := hb₁
    cases hty'
    obtain ⟨htailWF, hfresh, htr, hty⟩ := hmwf
    rw [htail] at htr hty
    refine ⟨ty, ?_, htr, hty⟩
    intro ty' hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty' at hrun
    have hfind' : c.lctx.find? H.fv =
        some (.cdecl tail.lctx.decls.size H.fv name ty bi .default) := by
      rw [← S.lctx_eq, hfind]
      change (tail.lctx.mkLocalDecl H.fv name ty bi).find? H.fv = _
      rw [LocalContext.find?_mkLocalDecl htailWF.tr.1.map_wf]
      simp
    simp only [LocalContext.get!, hfind', Except.ok.injEq] at hrun
    exact hrun.symm

/-- Recover every premise needed by the executable cached-parameter branch
from the retained local-context translation. -/
theorem ReusedParameterScope.typing
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {body : Expr}
    (H : ReusedParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS S.venv Us S.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS S.venv Us S.mlctx.vlctx
        stats.params[i]! param' ∧
      S.venv.HasType Us.length S.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? S.mlctx_wf.tr.wf.fvars_nodup hhead
  rcases hfull with hfull
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : S.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ S.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  have hlocal :=
    (S.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv
  rcases hlocal with ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← S.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [S.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ S.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases S.mlctx_wf.tr.find?_of_mem S.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact S.mlctx_wf.tr.wf.find?_wf S.checking.tr.wf hfind

/-- A closed source header starts the later-parameter traversal with an empty
free-variable scope. -/
noncomputable def ReusedParameterScope.ofNoFVars
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    ReusedParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

/-- Advance the reused-parameter scope after substituting cached parameter `i` and
normalizing the resulting body.  The next parameter's older suffix is
exactly the current cached declaration followed by the current older suffix.
-/
noncomputable def ReusedParameterScope.next
    {c : AddInductive.Context} {S : ContextSemantics c Us}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {body normalized : Expr}
    (H : ReusedParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow S.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    ReusedParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp :
        H.newer ++ currentEntry :: H.older =
          (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hopened : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older))
        (body.instantiate1 stats.params[i]!) := by
      rw [Expr.instantiate1_eq, H.parameter]
      exact H.openedFVars
    have hnormalized : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older)) normalized :=
      hbelow _ H.openedUpSet hopened
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

theorem ReusedParameterScope.olderLift
    {c : AddInductive.Context} {Us : List Name}
    {S : ContextSemantics c Us}
    {Hsuffix : ParameterContextSuffix S stats depth}
    (H : ReusedParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older S.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : S.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact S.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

theorem ReusedParameterScope.parameterDefEq
    {c : AddInductive.Context} {Us : List Name}
    {S : ContextSemantics c Us}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {params : List VExpr}
    (H : ReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    ∃ u, S.venv.IsDefEq Us.length H.older.toCtx
      (params[i]'(hparams.symm ▸ hi)) H.paramType (.sort u) := by
  have hcachedLength :=
    CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    VLCtx.toCtx_length_le H.newer
  have holderLe :=
    VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  let j := H.newer.toCtx.length
  have hj : j < params.reverse.length := by
    simp only [List.length_reverse, j, hnewerCtx, hparams,
      H.newerLength]
    omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  have hentry := VEnv.IsDefEqCtx.getElemRight
    S.checking.tr.wf.ordered hctx' hj
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have hsourceIndex : params.length - 1 - j = i := by
    rw [hparams, hjEq]
    omega
  have hsourceIndex' :
      params.length - 1 - H.newer.toCtx.length = i := by
    simpa [j] using hsourceIndex
  rcases hentry with ⟨u, hentry⟩
  simp [j] at hentry
  exact ⟨u, by
    simpa only [List.getElem_reverse, hsourceIndex'] using hentry⟩

theorem ReusedParameterScope.parameterPrefixDefEq
    {c : AddInductive.Context} {Us : List Name}
    {S : ContextSemantics c Us}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {params : List VExpr}
    (H : ReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    VEnv.IsDefEqCtx S.venv Us.length []
      (params.take i).reverse H.older.toCtx := by
  have hcachedLength :=
    CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    VLCtx.toCtx_length_le H.newer
  have holderLe :=
    VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  let j := H.newer.toCtx.length
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have htake : params.length - (j + 1) = i := by
    rw [hparams, hjEq]
    omega
  have htake' : params.length - (H.newer.toCtx.length + 1) = i := by
    simpa [j] using htake
  have hdrop := VEnv.IsDefEqCtx.dropHeads hctx' (j + 1)
  simp [j] at hdrop
  simpa [List.drop_reverse, htake'] using hdrop

theorem ReusedParameterScope.ownParameterDefEq
    {c : AddInductive.Context} {Us : List Name}
    {S : ContextSemantics c Us}
    {Hsuffix : ParameterContextSuffix S stats depth}
    {params ownParams : List VExpr}
    (H : ReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparamsLength : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hown : VEnv.IsDefEqCtx S.venv Us.length []
      params.reverse ownParams.reverse) :
    ∃ u, S.venv.IsDefEq Us.length H.older.toCtx
      (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using hown.length_eq
        omega)) H.paramType (.sort u) := by
  have hiparams : i < params.length := by omega
  have hlen : params.length = ownParams.length := by
    simpa using hown.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElem hown hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  have hcommonOwn : ∃ u, S.venv.IsDefEq Us.length
      (params.take i).reverse params[i]
      (ownParams[i]'(hlen ▸ hiparams)) (.sort u) := by
    simpa [List.getElem_reverse, List.drop_reverse, hlen.symm,
      Nat.sub_sub, htake, hindex] using hentry
  rcases hcommonOwn with ⟨u, hcommonOwn⟩
  have hprefix := H.parameterPrefixDefEq hi hparamsLength hctx
  have hcommonOwn' := hcommonOwn.defeqDFC
    S.checking.tr.wf.ordered hprefix
  rcases H.parameterDefEq hi hparamsLength hctx with
    ⟨cachedLevel, hcommonCached⟩
  have holderWF :=
    (H.lift.wf S.checking.tr.wf S.mlctx_wf.tr.wf).1
  exact ⟨cachedLevel, hcommonOwn'.symm.trans_r S.checking.tr.wf
    holderWF.toCtx hcommonCached⟩

end VerifyInductive
end Lean4Lean
