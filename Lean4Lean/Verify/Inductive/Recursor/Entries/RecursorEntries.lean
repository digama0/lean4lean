import Lean4Lean.Verify.Inductive.Rules.FromTemplates

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem CDeclArray.size
    (H : CDeclArray lctx xs) : xs.size = H.fvars.length := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simp

theorem CDeclArray.fvarsIn
    (H : CDeclArray lctx xs) (Hlctx : lctx.WF) :
    ∀ e ∈ xs, e.FVarsIn (· ∈ lctx.fvars) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  intro e he
  rw [List.mem_toArray, List.mem_map] at he
  rcases he with ⟨fv, hfv, rfl⟩
  simp only [Expr.FVarsIn]
  rcases declarations fv hfv with
    ⟨index, name, type, bi, kind, hfind⟩
  rw [Hlctx.find?_eq_find?_toList] at hfind
  rw [LocalContext.fvars]
  exact List.mem_map.mpr
    ⟨.cdecl index fv name type bi kind,
      List.mem_of_find?_eq_some hfind, rfl⟩

theorem CDeclArray.fvar_mem
    (H : CDeclArray lctx xs) (hfv : (.fvar fv : Expr) ∈ xs) :
    fv ∈ H.fvars := by
  rcases H with ⟨fvars, rfl, declarations⟩
  rw [List.mem_toArray, List.mem_map] at hfv
  rcases hfv with ⟨other, hother, heq⟩
  cases heq
  exact hother

/-- The binder domain selected by `LocalContext.mkForall` is the exact local
declaration type, simultaneously closed over the strictly earlier selected
free variables. This is what compares a domain of a generated recursor type with the
binder type recorded for it (`RecInfoBinderTypes`). -/
theorem LocalContext.mkBindingListN_forallBinderAt
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (LocalContext.mkBindingListN false lctx fvars body) i
      (type.abstractN (fvars.take i)) := by
  induction fvars generalizing i body with
  | nil => simp at hi
  | cons fv fvars ih =>
    have htailDecl : ∀ other ∈ fvars, ∃ index name type bi kind,
        lctx.find? other = some (.cdecl index other name type bi kind) := by
      intro other hother
      exact hdecl other (by simp [hother])
    have hnodupParts := List.nodup_cons.mp hnodup
    rw [LocalContext.mkBindingListN_cons
      (fun other hother => by
        rcases htailDecl other hother with
          ⟨index, name, type, bi, kind, hlookup⟩
        exact ⟨.cdecl index other name type bi kind, hlookup⟩)
      hnodup]
    cases i with
    | zero =>
      have hhead := hselected
      simp only [List.getElem_cons_zero] at hhead
      simp only [LocalContext.mkBindingList1N, hhead,
        List.take_zero, Expr.abstractN_nil]
      exact .here
    | succ i =>
      have hiTail : i < fvars.length := by simp at hi; omega
      rcases hdecl fv (by simp) with
        ⟨headIndex, headName, headType, headBi, headKind, hheadDecl⟩
      have htailSelected : lctx.find? fvars[i] =
          some (.cdecl index fvars[i] name type bi kind) := by
        simpa using hselected
      have Htail := ih htailDecl hnodupParts.2 i hiTail htailSelected
        (body := body)
      have Habstract := Htail.abstractN [fv] 0
      have hprefixNodup : (fv :: fvars.take i).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hnodupParts.1
          (List.mem_of_mem_take hmem),
          hnodupParts.2.take⟩
      have hdomain :
          (type.abstractN (fvars.take i)).abstractN [fv] i =
            type.abstractN (fv :: fvars.take i) := by
        have Hclose := Expr.abstractN_cons (List.nodup_cons.1 hprefixNodup).1 type 0
        simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hiTail)] using Hclose.symm
      simp only [Nat.zero_add] at Habstract
      rw [hdomain] at Habstract
      simpa [LocalContext.mkBindingList1N, hheadDecl] using
        Expr.ForallBinderAt.there Habstract

/-- `mkForall` specialization of the positional declaration theorem for an
explicit list of selected free variables. -/
theorem LocalContext.mkForall_fvars_forallBinderAt
    {lctx : LocalContext} {fvars : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (lctx.mkForall (fvars.map Expr.fvar).toArray body) i
      (type.abstractN (fvars.take i)) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_forallBinderAt hdecl hnodup i hi
    index name type bi kind hselected

/-- Sequential-model form of `mkForall_fvars_forallBinderAt` for closed binder
types. -/
theorem LocalContext.mkForall_fvars_forallBinderAtList
    {lctx : LocalContext} {fvars : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind))
    (hclosed : Closed type) :
    Expr.ForallBinderAt
      (lctx.mkForall (fvars.map Expr.fvar).toArray body) i
      (type.abstractList (fvars.take i)) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed
    (List.Nodup.sublist (List.take_sublist _ _) hnodup) hclosed]
  exact LocalContext.mkForall_fvars_forallBinderAt hdecl hnodup i hi index name
    type bi kind hselected

/-- `CDeclArray` form of the positional source-domain theorem. -/
theorem CDeclArray.forallBinderAt
    (H : CDeclArray c.lctx xs) (hnodup : H.fvars.Nodup)
    (D : FVarDeclAt c xs i) :
    Expr.ForallBinderAt (c.lctx.mkForall xs body) i
      (D.type.abstractN (H.fvars.take i)) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
  have hifvars : i < fvars.length := by simpa using D.inBounds
  have hselectedFVar : fvars[i] = D.fvar := by
    have hexpression : Expr.fvar fvars[i] = Expr.fvar D.fvar := by
      simpa [hifvars] using D.expression
    exact Expr.fvar.inj hexpression
  apply LocalContext.mkBindingListN_forallBinderAt declarations hnodup i
    hifvars D.index D.userName D.type D.binderInfo D.kind
  rw [hselectedFVar]
  exact D.declaration

/-- Sequential-model form of `forallBinderAt` for a locally closed declaration type. -/
theorem CDeclArray.forallBinderAtList
    (H : CDeclArray c.lctx xs) (hnodup : H.fvars.Nodup)
    (D : FVarDeclAt c xs i) (htype : Closed D.type) :
    Expr.ForallBinderAt (c.lctx.mkForall xs body) i
      (D.type.abstractList (H.fvars.take i)) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed hnodup.take htype]
  exact H.forallBinderAt hnodup D

/-- The hypothesis binder at position `j` in a generated minor is the exact
local declaration type used by the minor pass, closed first over preceding
hypotheses and then over the outer constructor fields. -/
theorem MinorPremiseType.hypothesisBinderAt
    (S : MinorPremiseType)
    (D : FVarDeclAt S.sourceFullContext S.hypotheses j) :
    Expr.ForallBinderAt S.origin (S.fields.size + j)
      ((D.type.abstractN (S.hypotheses_bound.fvars.take j)).abstractN
        S.fields_bound.fvars j) := by
  let Hselection := S.hypotheses_bound.toCDeclArray S.sourceFullWF
  have HinnerFull := Hselection.forallBinderAt S.hypotheses_nodup D
    (body := S.motiveApp)
  have Hinner : Expr.ForallBinderAt
      (S.sourceContext.mkForall S.hypotheses S.motiveApp) j
      (D.type.abstractN (S.hypotheses_bound.fvars.take j)) := by
    rw [← S.sourceContext_eq]
    exact HinnerFull
  have HinnerClosed := Hinner.abstractN S.fields_bound.fvars 0
  have Hfields := S.fieldTelescope
    (S.sourceContext.mkForall S.hypotheses S.motiveApp)
  have Hsource : Expr.ForallBinderAt S.sourceType (S.fields.size + j)
      ((D.type.abstractN (S.hypotheses_bound.fvars.take j)).abstractN
        S.fields_bound.fvars j) := by
    rw [S.sourceType_eq]
    simpa only [Nat.zero_add] using Hfields.prependBinderAt HinnerClosed
  have hconsumed : (S.sourceType.consumeTypeAnnotationsVerified S.sourceFullContext.env.isTypeAnnotationWrapper) = S.sourceType :=
    Hsource.consumeTypeAnnotationsVerified_eq_self
  have horigin : S.origin = S.sourceType :=
    S.unannotated_eq.symm.trans hconsumed
  rw [horigin]
  exact Hsource

/-- Sequential-model form of `hypothesisBinderAt` for a closed hypothesis
type. -/
theorem MinorPremiseType.hypothesisBinderAtList
    (S : MinorPremiseType)
    (D : FVarDeclAt S.sourceFullContext S.hypotheses j)
    (hclosed : Closed D.type) :
    Expr.ForallBinderAt S.origin (S.fields.size + j)
      ((D.type.abstractList (S.hypotheses_bound.fvars.take j)).abstractList
        S.fields_bound.fvars j) := by
  have h := S.hypothesisBinderAt D
  have hlen : S.hypotheses.size = S.hypotheses_bound.fvars.length := by
    simpa using congrArg Array.size S.hypotheses_bound.expressions
  have hj : j < S.hypotheses_bound.fvars.length := hlen ▸ D.inBounds
  rw [Expr.abstractN_eq_abstractList_of_closed
    (List.Nodup.sublist (List.take_sublist _ _) S.hypotheses_nodup) hclosed] at h
  rw [Expr.abstractN_eq_abstractList S.fields_nodup _ _ (by
    have hc := (Closed.abstractList_at (fvars := S.hypotheses_bound.fvars.take j)
      (depth := 0) (outer := 0) hclosed).looseBVarRange_le
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hc)] at h
  exact h

theorem CDeclArray.forallTelescope
    (H : CDeclArray lctx xs) (body : Expr) :
    Expr.ForallTelescope (lctx.mkForall xs body) xs.size
      (body.abstractN H.fvars) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simpa using LocalContext.mkForall_fvars_forallTelescope declarations

/-- Sequential-model form of `forallTelescope` for locally closed bodies. -/
theorem CDeclArray.forallTelescopeList
    (H : CDeclArray lctx xs) (body : Expr) (hnodup : H.fvars.Nodup)
    (hb : Closed body) :
    Expr.ForallTelescope (lctx.mkForall xs body) xs.size
      (body.abstractList H.fvars) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed hnodup hb]
  exact H.forallTelescope body

/-- Prepending one binder group to an existing telescope preserves
the inner telescope and abstracts its residual below exactly the inner arity. -/
theorem CDeclArray.prependTelescope
    (Hsel : CDeclArray lctx xs)
    (Hinner : Expr.ForallTelescope inner innerArity result) :
    Expr.ForallTelescope (lctx.mkForall xs inner)
      (xs.size + innerArity)
      (result.abstractN Hsel.fvars innerArity) := by
  exact (Hsel.forallTelescope inner).trans <| by
    simpa using Hinner.abstractN Hsel.fvars

/-- Prepend one binder group to an exact inner binder while
simultaneously closing its declaration type over the outer group.  The
explicit inner-prefix list makes this reusable for each successive group of
the generated recursor telescope. -/
theorem CDeclArray.prependBinderAtClosed
    {type : Expr}
    (Houter : CDeclArray lctx outer)
    (Hinner : Expr.ForallBinderAt inner i
      (type.abstractN innerPrefix))
    (hinnerLength : innerPrefix.length = i)
    (_hnodup : (Houter.fvars ++ innerPrefix).Nodup) :
    Expr.ForallBinderAt (lctx.mkForall outer inner) (outer.size + i)
      (type.abstractN (Houter.fvars ++ innerPrefix)) := by
  have Hclosed := Hinner.abstractN Houter.fvars 0
  have hdomain :
      (type.abstractN innerPrefix).abstractN Houter.fvars i =
        type.abstractN (Houter.fvars ++ innerPrefix) := by
    have Hclose := Expr.abstractN_after_inner
      (e := type) (outer := Houter.fvars) (inner := innerPrefix) (k := 0)
    simpa [hinnerLength] using Hclose
  have Hprefix := Houter.forallTelescope inner
  have Hresult := Hprefix.prependBinderAt Hclosed
  simpa only [Nat.zero_add, hdomain] using Hresult

def RecursorBinderGroups.residual
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (body : Expr) : Expr :=
  let afterMajor := body.abstractN H.major.fvars
  let afterIndices := afterMajor.abstractN H.indices.fvars 1
  let afterMinors := afterIndices.abstractN H.minors.fvars
    (recInfos[ownerIdx]!.indices.size + 1)
  let afterMotives := afterMinors.abstractN H.motives.fvars
    ((recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
  afterMotives.abstractN H.params.fvars
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)

def concreteRecursorResult
    (numMotives numMinors numIndices ownerIdx : Nat) : Expr :=
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indexVars := (List.ofFn fun i : Fin numIndices =>
    Expr.bvar (1 + (numIndices - 1 - i))).toArray
  .app (mkAppN (.bvar motiveOffset) indexVars) (.bvar 0)

private theorem indexBVarOffsets_eq (n : Nat) :
    List.ofFn (fun i : Fin n => 1 + (n - 1 - i)) =
      (List.range n).reverse.map (fun i => i + 1) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    simp only [List.getElem_ofFn]
    rw [List.getElem_map, List.getElem_reverse]
    simp only [List.length_range]
    rw [List.getElem_range]
    omega

/-- Translation of the normalized executable result is forced to be the
same de Bruijn application used by the abstract recursor specification. -/
theorem TrExprS.concreteRecursorResult_eq
    (howner : ownerIdx < numMotives)
    (htotal : numParams + numMotives + numMinors + numIndices + 1 ≤
      domains.length)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      result) :
    result = VExpr.mkApps
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (((List.range numIndices).reverse.map fun i => .bvar (i + 1)) ++
        [.bvar 0]) := by
  unfold concreteRecursorResult at H
  cases H with
  | app _ _ hfn hmajor =>
    have hmajorEq := TrExprS.bvar_eq_of_abstractForallContext hmajor
      (by omega)
    let indices := List.ofFn fun i : Fin numIndices =>
      1 + (numIndices - 1 - i)
    have hindexBound : ∀ i ∈ indices, i < domains.length := by
      intro i hi
      simp only [indices, List.mem_ofFn] at hi
      rcases hi with ⟨j, rfl⟩
      omega
    have hmotiveBound :
        1 + numIndices + numMinors + (numMotives - 1 - ownerIdx) <
          domains.length := by omega
    have hfn' := hfn
    unfold mkAppN at hfn'
    rw [← Array.foldl_toList] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (List.foldl mkApp
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))
        (List.ofFn ((fun i => Expr.bvar i) ∘
          fun i : Fin numIndices => 1 + (numIndices - 1 - i)))) _ at hfn'
    rw [← List.map_ofFn, List.foldl_map] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (indices.foldl (fun fn i => .app fn (.bvar i))
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))) _ at hfn'
    have hfnEq := TrExprS.foldl_bvars_eq domains Δ indices hindexBound
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext Hout
        hmotiveBound)
      hfn'
    rw [hmajorEq, hfnEq]
    unfold VExpr.mkApps
    have hindices : indices =
        (List.range numIndices).reverse.map (fun i => i + 1) := by
      exact indexBVarOffsets_eq numIndices
    rw [hindices, ← List.foldl_map]
    simp [Function.comp_def]

/-- With distinct binders (`NoAlias`), the five nested abstractions of the executable
compute to the de Bruijn result used by the abstract recursor specification. -/
theorem RecursorBinderGroups.residual_eq_concreteRecursorResult
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size) (hnoalias : H.NoAlias) :
    H.residual
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) =
      concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx := by
  let motiveFVars := H.motives.fvars
  let minorFVars := H.minors.fvars
  let indexFVars := H.indices.fvars
  let majorFVars := H.major.fvars
  have hmotivesLen : motiveFVars.length = recInfos.size := by
    have h := H.motives.size
    simpa [motiveFVars] using h.symm
  have hownerMotive : ownerIdx < motiveFVars.length := by
    simpa [hmotivesLen] using howner
  have hindicesLen : indexFVars.length =
      recInfos[ownerIdx]!.indices.size := by
    simpa [indexFVars] using H.indices.size.symm
  have hmajorLen : majorFVars.length = 1 := by
    simpa [majorFVars] using H.major.size.symm
  have hmotive : recInfos[ownerIdx]!.motive =
      .fvar motiveFVars[ownerIdx] := by
    have hget := congrArg (fun xs => xs[ownerIdx]!) H.motives.expressions
    simpa [motiveFVars, Array.getElem!_eq_getD, Array.getD, howner,
      hownerMotive] using hget
  have hindices : recInfos[ownerIdx]!.indices =
      (indexFVars.map Expr.fvar).toArray := H.indices.expressions
  have hmajor : recInfos[ownerIdx]!.major = .fvar majorFVars[0] := by
    have hget := congrArg (fun xs => xs[0]!) H.major.expressions
    simpa [majorFVars, hmajorLen] using hget
  let body : Expr := .app (mkAppN (.fvar motiveFVars[ownerIdx])
    (indexFVars.map Expr.fvar).toArray) (.fvar majorFVars[0])
  have hbody :
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) = body := by
    simp [body, hmotive, hindices, hmajor]
  rw [hbody]
  let parts := hnoalias.parts
  have hmotiveMajor : motiveFVars[ownerIdx] ∉ majorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simp [majorFVars, hmem]) rfl
  have hmotiveIndices : motiveFVars[ownerIdx] ∉ indexFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simp [indexFVars, hmem]) rfl
  have hmotiveMinors : motiveFVars[ownerIdx] ∉ minorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simp [minorFVars, hmem]) rfl
  have hindicesMajor : ∀ fv ∈ indexFVars, fv ∉ majorFVars := by
    intro fv hfv hmem
    exact parts.indices_major fv hfv fv hmem rfl
  let afterMajor := body.abstractN majorFVars
  have hmajorBound : 0 < majorFVars.length := by omega
  have hmajorOffset : majorFVars.length - 1 = 0 := by omega
  have hAfterMajor : afterMajor =
      .app (mkAppN (.fvar motiveFVars[ownerIdx])
        (indexFVars.map Expr.fvar).toArray) (.bvar 0) := by
    unfold afterMajor body
    rw [Expr.abstractN_app, Expr.abstractN_mkAppN,
      Expr.abstractN_fvar_of_not_mem hmotiveMajor,
      Expr.abstractN_fvarArray_of_disjoint indexFVars majorFVars 0
        hindicesMajor,
      Expr.abstractN_fvar_getElem parts.major 0 hmajorBound]
    simp [majorFVars, hmajorOffset]
  let indexBVars := (List.ofFn fun i : Fin indexFVars.length =>
    Expr.bvar (1 + (indexFVars.length - 1 - i))).toArray
  let afterIndices := afterMajor.abstractN indexFVars 1
  have hAfterIndices : afterIndices =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterIndices
    rw [hAfterMajor]
    unfold indexBVars
    rw [Expr.abstractN_app, Expr.abstractN_mkAppN,
      Expr.abstractN_fvar_of_not_mem hmotiveIndices,
      Expr.abstractN_fvarArray indexFVars 1 parts.indices]
    rw [Expr.abstractN_bvar_lt indexFVars (by omega : 0 < 1)]
  let afterMinors := afterIndices.abstractN minorFVars
    (indexFVars.length + 1)
  have hAfterMinors : afterMinors =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterMinors
    rw [hAfterIndices]
    unfold indexBVars
    rw [Expr.abstractN_app, Expr.abstractN_mkAppN,
      Expr.abstractN_fvar_of_not_mem hmotiveMinors,
      Expr.abstractN_indexBVars minorFVars indexFVars.length
        (indexFVars.length + 1) (by omega),
      Expr.abstractN_bvar_lt minorFVars (by omega : 0 < indexFVars.length + 1)]
  let motiveBase := minorFVars.length + indexFVars.length + 1
  let afterMotives := afterMinors.abstractN motiveFVars motiveBase
  have hAfterMotives : afterMotives =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    unfold afterMotives
    rw [hAfterMinors]
    unfold indexBVars
    rw [Expr.abstractN_app, Expr.abstractN_mkAppN,
      Expr.abstractN_fvar_getElem parts.motives ownerIdx hownerMotive,
      Expr.abstractN_indexBVars motiveFVars indexFVars.length motiveBase
        (by simp [motiveBase]; omega)]
    rw [Expr.abstractN_bvar_lt motiveFVars (by simp [motiveBase])]
  let allBase := motiveFVars.length + motiveBase
  have hAfterParams : afterMotives.abstractN H.params.fvars allBase =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    rw [hAfterMotives]
    unfold indexBVars
    rw [Expr.abstractN_app, Expr.abstractN_mkAppN,
      Expr.abstractN_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega),
      Expr.abstractN_indexBVars H.params.fvars indexFVars.length allBase
        (by simp [allBase, motiveBase]; omega),
      Expr.abstractN_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega)]
  dsimp only [RecursorBinderGroups.residual]
  change ((afterIndices.abstractN minorFVars
      (recInfos[ownerIdx]!.indices.size + 1)).abstractN motiveFVars
        ((recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)).abstractN H.params.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1) = _
  rw [← hindicesLen, H.minors.size, H.motives.size]
  simpa [afterMotives, afterMinors, afterIndices, afterMajor,
    concreteRecursorResult, indexBVars, motiveBase, allBase,
    motiveFVars, minorFVars, indexFVars,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAfterParams

/-- Exact executable telescope produced by the five nested `mkForall` calls of
`AddInductive.recursorType`. -/
theorem RecursorBinderGroups.forallTelescope
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (body : Expr) :
    Expr.ForallTelescope
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major] body)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1)
      (H.residual body) := by
  have hMajor := H.major.prependTelescope (.nil body)
  have hIndices := H.indices.prependTelescope hMajor
  have hMinors := H.minors.prependTelescope hIndices
  have hMotives := H.motives.prependTelescope hMinors
  have hParams := H.params.prependTelescope hMotives
  simpa [RecursorBinderGroups.residual, Nat.add_assoc] using hParams

/-- Every parameter slot has the same executable domain in every
generated recursor.  The owner-specific suffix only supplies the body below
the common parameter prefix. -/
theorem RecursorBinderGroups.parameterBinderAt
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c stats.params paramIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false) paramIdx
      (D.type.abstractN (H.params.fvars.take paramIdx)) := by
  dsimp only
  exact (H.params.forallBinderAt hnoalias.parts.params D).inferImplicit
    1000 false

theorem RecursorBinderGroups.parameterBinderAtList
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : FVarDeclAt c stats.params paramIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false) paramIdx
      (D.type.abstractList (H.params.fvars.take paramIdx)) := by
  dsimp only
  have h := H.parameterBinderAt hnoalias D
  dsimp only at h
  rwa [Expr.abstractN_eq_abstractList_of_closed
    (List.Nodup.sublist (List.take_sublist _ _) hnoalias.parts.params)
    (D.closed hl)] at h

/-- Every motive slot has a source domain independent of the
recursor owner.  It is closed over the common parameters and the strictly
earlier motives; the owner's indices and major occur only below this slot. -/
theorem RecursorBinderGroups.motiveBinderAt
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c
      (recInfos.map (·.motive)) motiveIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + motiveIdx)
      (D.type.abstractN
        (H.params.fvars ++ H.motives.fvars.take motiveIdx)) := by
  dsimp only
  let motiveBody :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) motiveBody
  let parts := hnoalias.parts
  have hmotiveFVars : motiveIdx < H.motives.fvars.length := by
    rw [← H.motives.size]
    exact D.inBounds
  have Hmotive : Expr.ForallBinderAt motiveSource motiveIdx
      (D.type.abstractN (H.motives.fvars.take motiveIdx)) := by
    exact H.motives.forallBinderAt parts.motives D
      (body := motiveBody)
  have HmotiveClosed := Hmotive.abstractN H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++ H.motives.fvars.take motiveIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, parts.motives.take, ?_⟩
    intro param hparam motive hmotive heq
    exact parts.params_later param hparam motive
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hmotive))) heq
  have hdomain :
      (D.type.abstractN (H.motives.fvars.take motiveIdx)).abstractN
          H.params.fvars motiveIdx =
        D.type.abstractN
          (H.params.fvars ++ H.motives.fvars.take motiveIdx) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars.take motiveIdx) (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hmotiveFVars)] using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have Hraw := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, hdomain] using HmotiveClosed)
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  simpa [motiveSource, motiveBody, hparamsLength] using
    Hraw.inferImplicit 1000 false

theorem RecursorBinderGroups.motiveBinderAtList
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : FVarDeclAt c
      (recInfos.map (·.motive)) motiveIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + motiveIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars.take motiveIdx)) := by
  dsimp only
  have h := H.motiveBinderAt hnoalias D
  dsimp only at h
  have hall : (H.params.fvars ++ (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))).Nodup := hnoalias
  have hnodup : (H.params.fvars ++ H.motives.fvars.take motiveIdx).Nodup :=
    List.Nodup.sublist (List.Sublist.append (List.Sublist.refl _)
      ((List.take_sublist _ _).trans (List.sublist_append_left _ _))) hall
  rwa [Expr.abstractN_eq_abstractList_of_closed hnodup (D.closed hl)] at h

/-- The owner motive slot of the executable recursor type closes the
exact motive declaration over precisely the common parameters and
strictly earlier motives.  The subsequent `inferImplicit` pass preserves
that domain and changes only binder annotations. -/
theorem RecursorBinderGroups.ownerMotiveBinderAt
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c
      (recInfos.map (·.motive)) ownerIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + ownerIdx)
      (D.type.abstractN
        (H.params.fvars ++ H.motives.fvars.take ownerIdx)) := by
  dsimp only
  let motiveBody :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) motiveBody
  let parts := hnoalias.parts
  have hownerFVars : ownerIdx < H.motives.fvars.length := by
    rw [← H.motives.size]
    exact D.inBounds
  have Hmotive : Expr.ForallBinderAt motiveSource ownerIdx
      (D.type.abstractN (H.motives.fvars.take ownerIdx)) := by
    exact H.motives.forallBinderAt parts.motives D
      (body := motiveBody)
  have HmotiveClosed := Hmotive.abstractN H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++ H.motives.fvars.take ownerIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, parts.motives.take, ?_⟩
    intro param hparam motive hmotive heq
    exact parts.params_later param hparam motive
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hmotive))) heq
  have hdomain :
      (D.type.abstractN (H.motives.fvars.take ownerIdx)).abstractN
          H.params.fvars ownerIdx =
        D.type.abstractN
          (H.params.fvars ++ H.motives.fvars.take ownerIdx) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars.take ownerIdx) (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hownerFVars)] using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have Hraw := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, hdomain] using HmotiveClosed)
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  simpa [motiveSource, motiveBody, hparamsLength] using
    Hraw.inferImplicit 1000 false

theorem RecursorBinderGroups.ownerMotiveBinderAtList
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : FVarDeclAt c
      (recInfos.map (·.motive)) ownerIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + ownerIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars.take ownerIdx)) := by
  dsimp only
  have h := H.ownerMotiveBinderAt hnoalias D
  dsimp only at h
  have hall : (H.params.fvars ++ (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))).Nodup := hnoalias
  have hnodup : (H.params.fvars ++ H.motives.fvars.take ownerIdx).Nodup :=
    List.Nodup.sublist (List.Sublist.append (List.Sublist.refl _)
      ((List.take_sublist _ _).trans (List.sublist_append_left _ _))) hall
  rwa [Expr.abstractN_eq_abstractList_of_closed hnodup (D.closed hl)] at h

/-- The flattened minor slot of the executable recursor type closes the
exact recorded minor declaration over all parameters, all motives, and the
strictly earlier minors. This is the executable-side identity used to compare
the translated generated domain with the typed minor premise. -/
theorem RecursorBinderGroups.minorBinderAt
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c
      (recInfos.flatMap (·.minors)) minorIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractN
        (H.params.fvars ++ H.motives.fvars ++
          H.minors.fvars.take minorIdx)) := by
  dsimp only
  let minorBody :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) minorBody
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have hminorFVars : minorIdx < H.minors.fvars.length := by
    rw [← H.minors.size]
    exact D.inBounds
  have Hminor : Expr.ForallBinderAt minorSource minorIdx
      (D.type.abstractN (H.minors.fvars.take minorIdx)) := by
    exact H.minors.forallBinderAt parts.minors D (body := minorBody)
  have HminorMotives := Hminor.abstractN H.motives.fvars 0
  have hmotivesMinorsNodup :
      (H.motives.fvars ++ H.minors.fvars.take minorIdx).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.motives, parts.minors.take, ?_⟩
    intro motive hmotive minor hminor heq
    exact parts.motives_later motive hmotive minor
      (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hminor))) heq
  have hdomainMotives :
      (D.type.abstractN (H.minors.fvars.take minorIdx)).abstractN
          H.motives.fvars minorIdx =
        D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.motives.fvars)
      (inner := H.minors.fvars.take minorIdx) (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars)] using Hclose
  have Hmotives := H.motives.forallTelescope minorSource
  have HthroughMotives := Hmotives.prependBinderAt (by
    simpa [Nat.zero_add, hdomainMotives] using HminorMotives)
  have HthroughParams := HthroughMotives.abstractN H.params.fvars 0
  have hprefixNodup :
      (H.params.fvars ++
        (H.motives.fvars ++ H.minors.fvars.take minorIdx)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, hmotivesMinorsNodup, ?_⟩
    intro param hparam later hlater heq
    rcases List.mem_append.mp hlater with hmotive | hminor
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inl hmotive)) heq
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl (List.mem_of_mem_take hminor))))) heq
  have hdomainParams :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (H.motives.fvars.length + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars ++ H.minors.fvars.take minorIdx)
      (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars), List.append_assoc]
      using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  have hmotivesLength : H.motives.fvars.length =
      (recInfos.map (·.motive)).size := by
    rw [← H.motives.size]
  have hmotivesLength' : H.motives.fvars.length = recInfos.size := by
    simpa using hmotivesLength
  have HrawBase := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, Nat.add_assoc] using HthroughParams)
  have hdomainParamsStats :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (recInfos.size + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    rw [← hmotivesLength']
    exact hdomainParams
  rw [hdomainParamsStats] at HrawBase
  have Hraw : Expr.ForallBinderAt
      (c.lctx.mkForall stats.params motiveSource)
      (H.params.fvars.length + (H.motives.fvars.length + minorIdx))
      (D.type.abstractN
        (H.params.fvars ++ (H.motives.fvars ++
          H.minors.fvars.take minorIdx))) := by
    simpa [hparamsLength, hmotivesLength, Nat.add_assoc] using
      HrawBase
  simpa [motiveSource, minorSource, minorBody, hparamsLength,
    hmotivesLength, Nat.add_assoc] using Hraw.inferImplicit 1000 false

theorem RecursorBinderGroups.minorBinderAtList
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : FVarDeclAt c
      (recInfos.flatMap (·.minors)) minorIdx) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars ++
          H.minors.fvars.take minorIdx)) := by
  dsimp only
  have h := H.minorBinderAt hnoalias D
  dsimp only at h
  have hall : (H.params.fvars ++ (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))).Nodup := hnoalias
  have hnodup : (H.params.fvars ++ H.motives.fvars ++
      H.minors.fvars.take minorIdx).Nodup := by
    rw [List.append_assoc]
    exact List.Nodup.sublist (List.Sublist.append (List.Sublist.refl _)
      (List.Sublist.append (List.Sublist.refl _)
        ((List.take_sublist _ _).trans (List.sublist_append_left _ _)))) hall
  rwa [Expr.abstractN_eq_abstractList_of_closed hnodup (D.closed hl)] at h

/-- The final major-premise slot is the exact major declaration
closed over all four preceding generated recursor groups. -/
theorem RecursorBinderGroups.majorBinderAt
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c #[recInfos[ownerIdx]!.major] 0) :
    let raw :=
      c.lctx.mkForall stats.params <|
      c.lctx.mkForall (recInfos.map (·.motive)) <|
      c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
      c.lctx.mkForall recInfos[ownerIdx]!.indices <|
      c.lctx.mkForall #[recInfos[ownerIdx]!.major]
        (.app (mkAppN recInfos[ownerIdx]!.motive
          recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
    Expr.ForallBinderAt (raw.inferImplicit 1000 false)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size)
      (D.type.abstractN
        (H.params.fvars ++ (H.motives.fvars ++
          (H.minors.fvars ++ H.indices.fvars)))) := by
  dsimp only
  let resultBody : Expr :=
    .app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major
  let majorSource :=
    c.lctx.mkForall #[recInfos[ownerIdx]!.major] resultBody
  let indexSource :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices majorSource
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) indexSource
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have HmajorBase : Expr.ForallBinderAt majorSource 0
      (D.type.abstractN (H.major.fvars.take 0)) := by
    exact H.major.forallBinderAt parts.major D (body := resultBody)
  have Hmajor : Expr.ForallBinderAt majorSource 0 (D.type.abstractN []) := by
    simpa only [List.take_zero] using HmajorBase
  have HthroughIndicesBase := H.indices.prependBinderAtClosed Hmajor
    (innerPrefix := []) (by simp) (by simpa using parts.indices)
  have HthroughIndices : Expr.ForallBinderAt indexSource
      recInfos[ownerIdx]!.indices.size
      (D.type.abstractN H.indices.fvars) := by
    simpa [indexSource] using HthroughIndicesBase
  have hminorIndices :
      (H.minors.fvars ++ H.indices.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.minors, parts.indices, ?_⟩
    intro minor hminor index hindex heq
    exact parts.minors_later minor hminor index
      (List.mem_append.mpr (Or.inl hindex)) heq
  have HthroughMinors := H.minors.prependBinderAtClosed HthroughIndices
    H.indices.size.symm hminorIndices
  have hminorIndicesLength :
      (H.minors.fvars ++ H.indices.fvars).length =
        (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size := by
    rw [List.length_append, ← H.minors.size, ← H.indices.size]
  have hmotiveMinorIndices :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.motives, hminorIndices, ?_⟩
    intro motive hmotive later hlater heq
    rcases List.mem_append.mp hlater with hminor | hindex
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inl hminor)) heq
    · exact parts.motives_later motive hmotive later
        (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl hindex)))) heq
  have HthroughMotives := H.motives.prependBinderAtClosed HthroughMinors
    hminorIndicesLength hmotiveMinorIndices
  have hmotiveMinorIndicesLength :
      (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars)).length =
        (recInfos.map (·.motive)).size +
          ((recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size) := by
    rw [List.length_append, hminorIndicesLength, ← H.motives.size]
  have hparamMotiveMinorIndices :
      (H.params.fvars ++ (H.motives.fvars ++
        (H.minors.fvars ++ H.indices.fvars))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨parts.params, hmotiveMinorIndices, ?_⟩
    intro param hparam later hlater heq
    rcases List.mem_append.mp hlater with hmotive | hlater
    · exact parts.params_later param hparam later
        (List.mem_append.mpr (Or.inl hmotive)) heq
    · rcases List.mem_append.mp hlater with hminor | hindex
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inl hminor)))) heq
      · exact parts.params_later param hparam later
          (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inr
              (List.mem_append.mpr (Or.inl hindex)))))) heq
  have Hraw := H.params.prependBinderAtClosed HthroughMotives
    hmotiveMinorIndicesLength hparamMotiveMinorIndices
  simpa [motiveSource, minorSource, indexSource, majorSource, resultBody,
    Nat.add_assoc] using Hraw.inferImplicit 1000 false

/-- The translation of the installed `.recInfo` also shows that the generated recursor
constant is well formed. -/
theorem RecursorBinderGroups.recursorWF_of_recInfo
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (info : RecursorVal) (recursor : VConstVal)
    (Hinfo : TrConstVal safety env (.recInfo info) recursor)
    (htype : info.type =
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false) :
    recursor.toVConstant.WF env := by
  have htranslated : TrExprS env info.levelParams [] info.type
      recursor.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using Hinfo.1.2.2
  rw [htype] at htranslated
  have hpre := TrExprS.of_inferImplicit htranslated
  have Htel := H.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  have hpositive : 0 < stats.params.size +
      (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 := by omega
  have hwf := TrExprS.isType_of_forallTelescope Htel hpositive hpre
  have huvars : info.levelParams.length = recursor.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hinfo.1.2.1
  rw [huvars] at hwf
  exact hwf

/-- Typing of the generated recursor types, read off the executable's check
(`checkRecursorTypes`): every executable recursor telescope translates, before the
annotation-only `inferImplicit` pass, to a well-formed abstract type in the environment
before the recursors are installed (the recursor-checking environment). -/
structure TrRecursorTypes
    (env : VEnv) (lparams : List Name) (elimLevel : Level)
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo) : Prop where
  notPartial : c.safety ≠ .partial
  typeAt : ∀ owner (_howner : owner < indTypes.size),
    ∃ type : VExpr,
      TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos c.lctx
          owner) type ∧
      env.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length [] type

/-- Soundness of the executable pre-installation validation loop.  Each
successful iteration checks the fully closed generated recursor type with the
recursor's exact universe parameters; erasing `inferImplicit` recovers the
pre-annotation telescope used by `TrRecursorTypes`. -/
theorem AddInductive.declareRecursors.checkRecursorTypes.translationsWF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (hmode : c.fuel.cacheMode.Sound venv)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array AddInductive.RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat) :
    (AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
      recInfos numMinors numMotives all lctx k isUnsafe lparams dIdx c).WF
      fun _ => ∀ owner, dIdx ≤ owner →
        (howner : owner < indTypes.size) →
        ∃ type : VExpr,
          TrExprS venv (AddInductive.getRecLevelParams elimLevel lparams) []
            (AddInductive.declareRecursors.recursorType stats recInfos lctx
              owner) type ∧
          venv.IsType
            (AddInductive.getRecLevelParams elimLevel lparams).length []
            type := by
  rw [AddInductive.declareRecursors.checkRecursorTypes]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    let info := AddInductive.declareRecursors.recursorInfo stats indTypes
      elimLevel recInfos numMinors numMotives all lctx k isUnsafe lparams
      dIdx []
    refine (AddInductive.declareRecursors.checkRecursorType.WF Hvalid info hmode).bind
      fun _ ⟨type, Htype, HisType⟩ => ?_
    have Htype' : TrExprS venv
        (AddInductive.getRecLevelParams elimLevel lparams) []
        (AddInductive.declareRecursors.recursorType stats recInfos lctx
          dIdx) type := by
      apply TrExprS.of_inferImplicit
        (numParams := 1000) (considerRange := false)
      simpa [info, AddInductive.declareRecursors.recursorInfo] using Htype
    have HisType' : venv.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length [] type := by
      simpa [info, AddInductive.declareRecursors.recursorInfo] using HisType
    refine (AddInductive.declareRecursors.checkRecursorTypes.translationsWF
      Hvalid hmode stats indTypes elimLevel recInfos numMinors numMotives
      all lctx k isUnsafe lparams (dIdx + 1)).mono
        fun _ Htail owner hdone howner => ?_
    by_cases heq : owner = dIdx
    · subst owner
      exact ⟨type, Htype', HisType'⟩
    · exact Htail owner (by omega) howner
  · rw [dif_neg hidx]
    exact Except.WF.pure fun owner _ howner =>
      False.elim (hidx (by omega))
termination_by indTypes.size - dIdx

/-- The executable validation loop `checkRecursorTypes` supplies the recursor-type
translations `TrRecursorTypes` used by the installation loop. The only premise beyond the
checking environment excludes `.partial`, which inductive checking never uses and whose
visibility order is incompatible with the generated `isUnsafe` bit. -/
theorem AddInductive.declareRecursors.checkRecursorTypes.trRecursorTypesWF
    (Hvalid : CheckingEnv.Valid c.safety c.env venv)
    (hmode : c.fuel.cacheMode.Sound venv)
    (hnotPartial : c.safety ≠ .partial)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array AddInductive.RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) :
    (AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
      recInfos numMinors numMotives all lctx k isUnsafe lparams 0 c).WF
      fun _ => TrRecursorTypes venv lparams elimLevel
        { c with lctx := lctx } stats indTypes recInfos := by
  refine (AddInductive.declareRecursors.checkRecursorTypes.translationsWF
    Hvalid hmode stats indTypes elimLevel recInfos numMinors numMotives
    all lctx k isUnsafe lparams 0).mono fun _ Hall => ?_
  exact {
    notPartial := hnotPartial
    typeAt := fun owner howner => Hall owner (Nat.zero_le _) howner }

/-- The exact result of the executable, context-independent K eligibility
check. Recording the returned value prevents generated recursor metadata from
enabling K for a family the executable check rejected. -/
def KEligible (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (k : Bool) : Prop :=
  ∀ c, AddInductive.isKTarget stats indTypes c = .ok k

/-- The same executable check cannot certify two different metadata bits. -/
theorem KEligible.unique (H : KEligible stats indTypes k)
    (H' : KEligible stats indTypes k') (c : AddInductive.Context) : k = k' :=
  Except.ok.inj ((H c).symm.trans (H' c))

private theorem isKTarget_context_eq
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (c d : AddInductive.Context) :
    AddInductive.isKTarget stats indTypes c =
      AddInductive.isKTarget stats indTypes d := by
  rcases indTypes with ⟨xs⟩
  cases xs with
  | nil => rfl
  | cons ind rest =>
    cases rest with
    | cons next rest => rfl
    | nil =>
      unfold AddInductive.isKTarget
      unfold AddInductive.isLargeEliminator.match_4
      simp only [Array.size,
        List.length_cons, List.length_nil, ↓reduceDIte, Array.getLit]
      split
      · change (match ind.ctors with
          | [ctor] => pure (AddInductive.isKTarget.loop stats 0 ctor.type)
          | _ => pure false : AddInductive.M Bool) c =
          (match ind.ctors with
          | [ctor] => pure (AddInductive.isKTarget.loop stats 0 ctor.type)
          | _ => pure false : AddInductive.M Bool) d
        cases ind.ctors with
        | nil => rfl
        | cons ctor ctors => cases ctors <;> rfl
      · rfl

/-- The result of the executable K check satisfies `KEligible`. -/
theorem AddInductive.isKTarget.checkedWF
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (c : AddInductive.Context) :
    (AddInductive.isKTarget stats indTypes c).WF
      (KEligible stats indTypes) := by
  intro k hk c'
  exact (isKTarget_context_eq stats indTypes c' c).trans hk

private theorem isKTarget_loop_bound (stats : AddInductive.InductiveStats) (type : Expr)
    (i : Nat) (h : AddInductive.isKTarget.loop stats i type = true) :
    AddInductive.constructorArity type ≤ stats.params.size - i := by
  induction type generalizing i <;>
    simp_all [AddInductive.isKTarget.loop, AddInductive.constructorArity]
  rename_i _ _ _ _ _ ih
  obtain ⟨hless, hloop⟩ := h
  have := ih (i + 1) hloop
  omega

/-- A successful K check permits one propositional family with one constructor
and no constructor binders beyond the common parameters. -/
theorem KEligible.true_shape
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (H : KEligible stats indTypes true) (c : AddInductive.Context) :
    ∃ ind ctor, indTypes = #[ind] ∧ stats.resultLevel.isAlwaysZero = true ∧
      ind.ctors = [ctor] ∧ AddInductive.constructorArity ctor.type ≤ stats.params.size := by
  have h := H c
  rcases indTypes with ⟨xs⟩
  cases xs with
  | nil => cases h
  | cons ind rest =>
    cases rest with
    | cons next rest => cases h
    | nil =>
      unfold AddInductive.isKTarget at h
      unfold AddInductive.isLargeEliminator.match_4 at h
      simp only [Array.size, List.length_cons, List.length_nil, ↓reduceDIte,
        Array.getLit] at h
      split at h
      · rename_i hzero
        change (match ind.ctors with
          | [ctor] => pure (AddInductive.isKTarget.loop stats 0 ctor.type)
          | _ => pure false : AddInductive.M Bool) c = .ok true at h
        cases hctors : ind.ctors with
        | nil => simp only [hctors] at h; cases h
        | cons ctor ctors =>
          cases ctors with
          | nil =>
            simp only [hctors] at h
            have hloop : AddInductive.isKTarget.loop stats 0 ctor.type = true :=
              Except.ok.inj h
            exact ⟨ind, ctor, rfl, hzero, hctors,
              by simpa using isKTarget_loop_bound stats ctor.type 0 hloop⟩
          | cons next rest => simp only [hctors] at h; cases h
      · cases h

/-- The entry installed by one iteration of the executable recursor loop
(`declareRecursors.loop`), with the metadata needed to connect it to the generated
recursor and its typing. -/
structure GeneratedRecursorEntry
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (ownerIdx : Nat) (entry : ConstantInfo × VConstVal) where
  info : RecursorVal
  source_eq : entry.1 = .recInfo info
  translated : TrConstVal safety env (.recInfo info) entry.2
  levels : info.levelParams =
    AddInductive.getRecLevelParams elimLevel lparams
  name : info.name = Lean.mkRecName indTypes[ownerIdx]!.name
  all : info.all = (indTypes.map (·.name)).toList
  kChecked : KEligible stats indTypes info.k
  /-- The executable recursor pass chooses safety from the checking context.
  This exact bit is needed when an unsafe block is hidden from the
  partial and safe environment views. -/
  isUnsafe : info.isUnsafe = (c.safety != .safe)
  numParams : info.numParams = stats.params.size
  numIndices : info.numIndices = stats.nindices[ownerIdx]!
  numMotives : info.numMotives = (recInfos.map (·.motive)).size
  numMinors : info.numMinors = (recInfos.flatMap (·.minors)).size
  type : info.type =
    (c.lctx.mkForall stats.params <|
     c.lctx.mkForall (recInfos.map (·.motive)) <|
     c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
     c.lctx.mkForall recInfos[ownerIdx]!.indices <|
     c.lctx.mkForall #[recInfos[ownerIdx]!.major]
       (.app (mkAppN recInfos[ownerIdx]!.motive
         recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
      1000 false
  rules : RecursorRulesSyntax indTypes stats
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[ownerIdx]!.ctors (recursorMinorOffset indTypes ownerIdx)
    info.rules
  /-- The installed rules are literally the instantiations of the rule templates recorded
  by `mkRecInfos`, in the local context of the recursor construction. -/
  rules_eq : info.rules =
    recInfos[ownerIdx]!.ruleTemplates.toList.map fun blueprint =>
      blueprint.instantiate indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) c.lctx

def GeneratedRecursorEntry.ofRecursorInfo
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (numMinors numMotives : Nat) (all : List Name)
    (hnumMinors : numMinors = (recInfos.flatMap (·.minors)).size)
    (hnumMotives : numMotives = (recInfos.map (·.motive)).size)
    (k isUnsafe : Bool) (ownerIdx : Nat) (rules : List RecursorRule)
    (recursor : VConstVal)
    (hunsafe : isUnsafe = (c.safety != .safe))
    (hall : all = (indTypes.map (·.name)).toList)
    (hk : KEligible stats indTypes k)
    (Htr : TrConstVal safety env
      (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams ownerIdx rules)) recursor)
    (Hrules : RecursorRulesSyntax indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels)
      indTypes[ownerIdx]!.ctors (recursorMinorOffset indTypes ownerIdx)
      rules)
    (hrulesEq : rules =
      recInfos[ownerIdx]!.ruleTemplates.toList.map fun blueprint =>
        blueprint.instantiate indTypes stats (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) c.lctx) :
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos ownerIdx
      (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe
        lparams ownerIdx rules), recursor) where
  info := AddInductive.declareRecursors.recursorInfo stats indTypes
    elimLevel recInfos numMinors numMotives all c.lctx k isUnsafe lparams
    ownerIdx rules
  source_eq := rfl
  translated := Htr
  levels := rfl
  name := rfl
  all := hall
  kChecked := hk
  isUnsafe := by
    simp [AddInductive.declareRecursors.recursorInfo, hunsafe]
  numParams := rfl
  numIndices := rfl
  numMotives := by
    simpa [AddInductive.declareRecursors.recursorInfo] using hnumMotives
  numMinors := by
    simpa [AddInductive.declareRecursors.recursorInfo] using hnumMinors
  type := rfl
  rules := Hrules
  rules_eq := hrulesEq

/-- Output invariant of the executable recursor loop: one `GeneratedRecursorEntry` per
recursor info. -/
structure GeneratedRecursors
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  length : entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

/-- Append-oriented form matching the `for dIdx in [:indTypes.size]` loop. -/
structure GeneratedRecursorsPrefix
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  covered : entries.length ≤ recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

/-- Suffix-oriented traversal invariant used by the explicit recursive
`declareRecursors.loop`. Unlike `GeneratedRecursorsPrefix`, this form can be
applied recursively at an arbitrary owner index without carrying an
accumulator through executable code. -/
structure GeneratedRecursorsRange
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (start : Nat) (entries : List (ConstantInfo × VConstVal)) where
  covered : start + entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos (start + i) entries[i]

/-- Typed companion to `GeneratedRecursorsRange`. The range invariant records the
executable and abstract recursor entries and their rules; this one records, for the same
owners, the typed rules (`TypedRecursorRules`) with their field classification and typed
recursive calls. It does not repeat the translated recursor value. -/
structure TypedRecursorRulesRange
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (Horigins : RecInfoBinderTypes semanticRoot recInfos)
    (elimLevel : Level)
    (parameterDecls : VLCtx)
    (start : Nat) (entries : List (ConstantInfo × VConstVal)) where
  covered : start + entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    ∃ info : RecursorVal,
      entries[i].1 = .recInfo info ∧
      ∃ Hrules : TypedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) Rroot decl
          (start + i) indTypes[start + i]!.ctors
          (recursorMinorOffset indTypes (start + i)) info.rules,
        Nonempty (Hrules.MotiveAt recInfos elimLevel) ∧
        ∀ localIndex
            (hctor : localIndex < indTypes[start + i]!.ctors.length)
            (hrule : localIndex < info.rules.length),
          ∃ Hrule : RecursorRuleSyntax indTypes stats
              (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
              (AddInductive.getRecLevels elimLevel stats.levels)
              indTypes[start + i]!.ctors[localIndex]
              (recursorMinorOffset indTypes (start + i) + localIndex)
              info.rules[localIndex],
            ∃ S : Hrule.Semantics Rroot decl (start + i),
              Nonempty (Hrule.MinorAt S recInfos elimLevel
                Horigins (start + i) localIndex) ∧
              S.parameterDecls = parameterDecls

def GeneratedRecursorsRange.atZero
    (H : GeneratedRecursorsRange safety env lparams elimLevel c stats
      indTypes recInfos 0 entries)
    (hcomplete : entries.length = recInfos.size) :
    GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries where
  length := hcomplete
  entry i hi := by simpa using H.entry i hi

theorem GeneratedRecursors.nonInductive
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries) :
    ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ ConstantInfo.inductInfo inductiveValue := by
  intro info value hmem inductiveValue
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have Hentry := H.entry i hi
  rw [heq] at Hentry
  have hsource : info = .recInfo Hentry.info := by
    simpa using Hentry.source_eq
  rw [hsource]
  simp

/-- Generated recursor entries cannot introduce constructor metadata. -/
theorem GeneratedRecursors.nonConstructor
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries) :
    ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ constructorValue,
        info ≠ ConstantInfo.ctorInfo constructorValue := by
  intro info value hmem constructorValue
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
  have Hentry := H.entry i hi
  rw [heq] at Hentry
  have hsource : info = .recInfo Hentry.info := by
    simpa using Hentry.source_eq
  rw [hsource]
  simp

def GeneratedRecursorsPrefix.empty
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo) :
    GeneratedRecursorsPrefix safety env lparams elimLevel c stats indTypes
      recInfos [] where
  covered := Nat.zero_le _
  entry _ hi := by simp at hi

/-- Every family index of the block names a generated recursor. -/
theorem GeneratedRecursors.recursorName_mem
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (hrecords : recInfos.size = indTypes.size)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    Lean.mkRecName indTypes[ownerIdx]!.name ∈
      (entries.map Prod.snd).map (·.name) := by
  have hentry : ownerIdx < entries.length := by
    rw [H.length, hrecords]
    exact howner
  let E := H.entry ownerIdx hentry
  have htranslatedName : E.info.name = entries[ownerIdx].2.name := by
    exact E.translated.2
  have hname : entries[ownerIdx].2.name =
      Lean.mkRecName indTypes[ownerIdx]!.name := by
    rw [← htranslatedName, E.name]
  rw [← hname]
  exact List.mem_map.mpr ⟨entries[ownerIdx].2,
    List.mem_map.mpr ⟨entries[ownerIdx], List.getElem_mem hentry, rfl⟩,
    rfl⟩

theorem GeneratedRecursors.recursorsWF
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params) :
    ∀ recursor ∈ entries.map Prod.snd, recursor.toVConstant.WF env := by
  intro recursor hrec
  rcases List.mem_iff_getElem.mp hrec with ⟨i, hi, heq⟩
  have hentry : i < entries.length := by simpa using hi
  have heqTarget : entries[i].2 = recursor := by simpa using heq
  subst recursor
  have howner : i < recInfos.size := by simpa [H.length] using hentry
  let Hlocal := Hbindings.toRecursorBinderGroups Hc Hparams i howner
  let E := H.entry i hentry
  have hwf := Hlocal.recursorWF_of_recInfo E.info entries[i].2
    E.translated E.type
  simpa using hwf

end VerifyInductive
end Lean4Lean
