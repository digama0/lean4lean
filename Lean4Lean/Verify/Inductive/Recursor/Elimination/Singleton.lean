import Lean4Lean.Verify.Inductive.Context.TypeAnnotations
import Lean4Lean.Verify.Inductive.Recursor.Elimination.Large
import Lean4Lean.Verify.Typing.RawShape

/-! The abstract reading of a successful singleton check (`LargeEliminationCheck`): the
constructor's translated telescope is a `SingletonTelescope`, in which every non-parameter
binder is a proof or occurs literally among the result arguments. This is the shape that
singleton elimination (`Instance.Admissible`) needs.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive

/-- A literal field variable occurs among the result arguments after all
remaining constructor binders are opened. -/
inductive ResultBVar : Nat → VExpr → Prop
  | here : e.getAppFnArgs.1 = .const name levels →
      .bvar i ∈ e.getAppFnArgs.2 → ResultBVar i e
  | under : ResultBVar (i + 1) body → ResultBVar i (.forallE domain body)

/-- The source telescope interpreted by the successful singleton check.
Every non-parameter binder is a proof or an exact result argument. -/
inductive SingletonTelescope (env : VEnv) (U nparams : Nat) :
    List VExpr → Nat → VExpr → Prop
  | done : e.forallArity = 0 → SingletonTelescope env U nparams ctx i e
  | field : env.IsType U ctx domain →
    (i < nparams ∨ env.HasType U ctx domain (.sort .zero) ∨ ResultBVar 0 body) →
    SingletonTelescope env U nparams (domain :: ctx) (i + 1) body →
    SingletonTelescope env U nparams ctx i (.forallE domain body)

private theorem constHead_instantiate1 {e : Expr}
    (h : e.getAppFn = .const name levels) :
    (e.instantiate1' (.fvar fv) d).getAppFn = .const name levels := by
  induction e with
  | app fn arg ih _ => exact ih h
  | const => exact h
  | _ => cases h

theorem Expr.ForallSpine.instantiateFVar
    (H : Expr.ForallSpine e arity) :
    Expr.ForallSpine (e.instantiate1' (.fvar fv) d) arity := by
  induction H generalizing d with
  | codomain hhead => exact .codomain (constHead_instantiate1 hhead)
  | step _ ih => exact .step ih

theorem ResultBVar.of_rawShape (H : ResultBVar i e)
    (hshape : VExpr.RawShapeRel e e') : ResultBVar i e' := by
  induction H generalizing e' with
  | here hhead hmem =>
    obtain ⟨hhead', hargs⟩ := hshape.symm.const_spine_inv hhead
    obtain ⟨arg, harg, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hargs _ hmem
    have heq := hrel.bvar_inv rfl
    exact .here hhead' (heq ▸ harg)
  | under H ih =>
    obtain ⟨domain', body', rfl, hbody⟩ := hshape.symm.forallE_inv rfl
    exact .under (ih hbody.symm)

theorem ResultBVar.wrapForalls (H : ResultBVar i (VExpr.wrapForalls fields result))
    (hresult : result.forallArity = 0) :
    .bvar (i + fields.length) ∈ result.getAppFnArgs.2 := by
  induction fields generalizing i with
  | nil =>
    cases H with
    | here _ hmem => exact hmem
    | under => cases hresult
  | cons field fields ih =>
    cases H with
    | here hhead => cases hhead
    | under hb => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hb

theorem SingletonTelescope.dropParams
    (H : SingletonTelescope env U nparams ctx i (VExpr.wrapForalls params tail)) :
    SingletonTelescope env U nparams (params.reverse ++ ctx) (i + params.length) tail := by
  induction params generalizing ctx i with
  | nil => simpa [VExpr.wrapForalls] using H
  | cons param params ih =>
    cases H with
    | done h => cases h
    | field _ _ hb =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih hb

theorem SingletonTelescope.fieldAt
    (H : SingletonTelescope env U nparams ctx count (VExpr.wrapForalls fields result))
    (hcount : nparams ≤ count) (hresult : result.forallArity = 0)
    (i : Nat) (hi : i < fields.length) :
    env.HasType U ((fields.take i).reverse ++ ctx) fields[i] (.sort .zero) ∨
      .bvar (fields.length - 1 - i) ∈ result.getAppFnArgs.2 := by
  induction fields generalizing i ctx count with
  | nil => simp at hi
  | cons field fields ih =>
    cases H with
    | done h => cases h
    | field _ hcond hb =>
      cases i with
      | zero =>
        rcases hcond with hparam | hproof | hindex
        · omega
        · exact .inl hproof
        · exact .inr (by simpa using hindex.wrapForalls hresult)
      | succ i =>
        have h := ih hb (by omega) i (by simpa using hi)
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
          Nat.sub_sub, Nat.add_comm] using h

theorem SingletonTelescope.defeqCtx
    (H : SingletonTelescope env U nparams ctx count target)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx U base ctx ctx') :
    SingletonTelescope env U nparams ctx' count target := by
  induction H generalizing ctx' with
  | done h => exact .done h
  | field hdom hcond _ ih =>
    obtain ⟨u, hdom⟩ := hdom
    refine .field ⟨u, hdom.defeqDFC henv hctx⟩ ?_ (ih (.succ hctx hdom))
    rcases hcond with hp | hh | hi
    · exact .inl hp
    · exact .inr (.inl (hh.defeqDFC henv hctx))
    · exact .inr (.inr hi)

/-- Proof-field classification is invariant under typed equality. Literal
result occurrences additionally use the raw shape relation (`VExpr.RawShapeRel`). -/
theorem SingletonTelescope.of_defeq
    (H : SingletonTelescope env U nparams ctx count target)
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType U))
    (heq : env.IsDefEqU U ctx target target')
    (hshape : VExpr.RawShapeRel target target') :
    SingletonTelescope env U nparams ctx count target' := by
  induction H generalizing target' with
  | done h =>
    apply SingletonTelescope.done
    cases target' with
    | forallE d b =>
      obtain ⟨_, _, rfl, _⟩ := hshape.forallE_inv rfl
      cases h
    | _ => rfl
  | @field ctx domain count body hdom hcond htail ih =>
    obtain ⟨domain', body', rfl, hbodyShape⟩ := hshape.symm.forallE_inv rfl
    obtain ⟨⟨u, hdomains⟩, ⟨v, hbodies⟩⟩ := heq.forallE_inv henv hctx
    have hctx' : OnCtx (domain :: ctx) (env.IsType U) := ⟨hctx, hdom⟩
    have ht := ih hctx' ⟨_, hbodies⟩ hbodyShape.symm
    have hconvert : env.IsDefEqCtx U [] (domain :: ctx) (domain' :: ctx) :=
      .succ (.refl hctx) hdomains
    refine .field ⟨u, hdomains.hasType.2⟩ ?_ (ht.defeqCtx henv.ordered hconvert)
    rcases hcond with hp | hh | hi
    · exact .inl hp
    · exact .inr (.inl (hh.defeqU_l henv hctx ⟨_, hdomains⟩))
    · exact .inr (.inr (hi.of_rawShape hbodyShape.symm))

/-- A singleton telescope in a larger environment is one in a smaller environment in which
the target is a type: a domain typed in the smaller environment that is a proof in the
larger one already has sort `Prop` in the smaller one. -/
theorem SingletonTelescope.of_mono
    (H : SingletonTelescope env' U nparams ctx count target)
    (hle : env ≤ env') (henv : env.WF) (henv' : env'.WF)
    (hctx : OnCtx ctx (env.IsType U)) (htype : env.IsType U ctx target) :
    SingletonTelescope env U nparams ctx count target := by
  induction H with
  | done h => exact .done h
  | field _ hcond _ ih =>
    obtain ⟨hdom, hbody⟩ := htype.forallE_inv henv.ordered
    refine .field hdom ?_ (ih ⟨hctx, hdom⟩ hbody)
    rcases hcond with hp | hh | hi
    · exact .inl hp
    · obtain ⟨u, hu⟩ := hdom
      have hsort := (hu.mono hle).uniqU henv' (hctx.mono (VEnv.IsType.mono hle)) hh
      have heq := hsort.sort_inv henv' (hctx.mono (VEnv.IsType.mono hle))
      exact .inr (.inl (.defeqDF (.sortDF (hu.sort_r henv.ordered hctx) trivial heq) hu))
    · exact .inr (.inr hi)

/-- The singleton checker starts with a closed constructor type, so none
of the ambient runtime variables belong to its source telescope. -/
def checkInductiveTypes.loopType.FrontScopeEmbedding.empty (Hc : ContextWF c) :
    checkInductiveTypes.loopType.FrontScopeEmbedding Hc.venv c.lparams [] Hc.mlctx.vlctx := by
  let W := VLCtx.FVLift.to_append [] Hc.mlctx.noBV
  refine {
    expanded := Hc.mlctx.vlctx
    shift := .skipN .refl Hc.mlctx.vlctx.toCtx.length
    lift := by simpa using W.toFVLift'
    frontSourceDomains := []
    frontExpandedDomains := []
    front := .zero (by simpa using W.toFVLift')
    context := .refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    upset := by simpa using IsFVarUpSet.suffixFVars [] Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    noBV := rfl
    noIndConsts := fun _ => nofun
    sourceTelescope := .nil
    wf := trivial }

/-- Pending index requirements remain attached to their actual named field
through the exact binder opening performed by the executable check. -/
theorem LargeEliminationCheck.singletonTelescope
    (H : LargeEliminationCheck stats c source i required)
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hspine : Expr.ForallSpine source arity)
    (hnarrow : TrExprS Hc.venv c.lparams scope source target)
    (hfull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source fullTarget) :
    SingletonTelescope Hc.venv c.lparams.length stats.params.size scope.toCtx i target ∧
    ∀ fv, Expr.fvar fv ∈ required.toList → ∀ index type,
      scope.find? (.inr fv) = some (.bvar index, type) → ResultBVar index target := by
  induction H generalizing scope target fullTarget arity with
  | @done c source i required hnot hcontains =>
    cases Hspine with
    | step => cases hnot
    | codomain hhead =>
      obtain ⟨levels, args, hspine, _, hargs⟩ :=
        checkPositivityStep.TrExprS.constAppSpine hnarrow hhead
      have harity := VExpr.forallArity_eq_zero_of_getAppFnArgs hspine
      refine ⟨.done harity, ?_⟩
      intro fv hfv index type hfind
      have hcontains' : source.getAppArgsList.contains (.fvar fv) = true := by
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hfv
        have hh := Array.all_eq_true.mp hcontains j (by simpa using hj)
        simp only [Array.getElem_toList] at heq
        rw [heq] at hh
        simpa [← Expr.getAppArgs_toList] using hh
      have hmem := LargeEliminationCheck.contains_bvar_of_fvar hargs hcontains' hfind
      exact .here (congrArg Prod.fst hspine) (by simpa [hspine] using hmem)
  | @param c name dom body bi i required hparam Htail ih =>
    cases hnarrow with
    | @forallE narrowDom narrowBody _ _ _ _ _ hdomType hbodyType hdomNarrow hbodyNarrow =>
      obtain ⟨fullForall, hfullForall, _⟩ := hfull
      cases hfullForall with
      | forallE hfullDomType _ hfullDom hfullBody =>
        obtain ⟨consumed, Hdom⟩ := consumeTypeAnnotationsCompat c Hc hfullDom hfullDomType
        rcases halign.forallE_align Hc.checking.tr.wf hdomNarrow hdomType hbodyNarrow with
          ⟨dom₀, _, hdom₀, hdom₀Type, _, _, _⟩
        obtain ⟨consumed₀, Hdom₀⟩ :=
          consumeTypeAnnotationsCompat _ Hc.atCheckLCtx hdom₀ hdom₀Type
        let Hnext := Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
        have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
        obtain ⟨domainLevel, hdomain⟩ := Hruntime.unannotatedDomain Hc Hdom hdomNarrow
        let Hruntime' := Hruntime.withIndex Hnext.mlctx_wf.tr.wf hdeps name bi dom hdomNarrow hdomain hdomType
        have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
          Hdom Hdom₀ hdomNarrow hdomType hdeps
        have hscopeWF := halign'.wf
        have hopened := hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
        rw [← Expr.instantiate1_eq] at hopened
        obtain ⟨fullBody, hfullBody', _⟩ := Hdom.body Hc hfullBody
        have hopenedFull := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType hfullBody'
        have hspineBody : ∃ n, Expr.ForallSpine body n := by
          cases Hspine with
          | codomain hh => cases hh
          | step hb => exact ⟨_, hb⟩
        obtain ⟨n, hn⟩ := hspineBody
        have hn' := hn.instantiateFVar (fv := ⟨c.ngen.curr⟩) (d := 0)
        rw [← Expr.instantiate1_eq] at hn'
        obtain ⟨htail, hrequired⟩ := ih Hnext Hruntime' halign' hn' hopened
          (hopenedFull.trExpr Hnext.checking.tr.wf Hnext.mlctx_wf.tr.wf)
        refine ⟨.field hdomType ?_ htail, ?_⟩
        · exact .inl hparam
        · intro fv hfv index type hfind
          apply ResultBVar.under
          have hfvMem : fv ∈ scope.fvars := VLCtx.find?_eq_some.mp ⟨_, hfind⟩
          have hne : fv ≠ ⟨c.ngen.curr⟩ := by
            have hfresh := hscopeWF.fvars_nodup
            simp only [VLCtx.fvars, List.filterMap_cons, Option.map_some, List.nodup_cons] at hfresh
            intro heq
            exact hfresh.1 (heq ▸ hfvMem)
          have hfind' := VLCtx.find?_vlam_ne
            (deps := (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList) (ty := narrowDom)
            (by simpa using hne.symm) hfind
          apply hrequired fv hfv (index + 1) _
          simpa [VExpr.lift, VExpr.liftN] using hfind'

  | @proof c name dom body bi i required result hfield hcheck hzero Htail ih =>
    cases hnarrow with
    | @forallE narrowDom narrowBody _ _ _ _ _ hdomType hbodyType hdomNarrow hbodyNarrow =>
      obtain ⟨fullForall, hfullForall, _⟩ := hfull
      cases hfullForall with
      | forallE hfullDomType _ hfullDom hfullBody =>
        obtain ⟨consumed, Hdom⟩ := consumeTypeAnnotationsCompat c Hc hfullDom hfullDomType
        rcases halign.forallE_align Hc.checking.tr.wf hdomNarrow hdomType hbodyNarrow with
          ⟨dom₀, _, hdom₀, hdom₀Type, _, _, _⟩
        obtain ⟨consumed₀, Hdom₀⟩ :=
          consumeTypeAnnotationsCompat _ Hc.atCheckLCtx hdom₀ hdom₀Type
        let Hnext := Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
        have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
        obtain ⟨domainLevel, hdomain⟩ := Hruntime.unannotatedDomain Hc Hdom hdomNarrow
        let Hruntime' := Hruntime.withIndex Hnext.mlctx_wf.tr.wf hdeps name bi dom hdomNarrow hdomain hdomType
        have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
          Hdom Hdom₀ hdomNarrow hdomType hdeps
        have hscopeWF := halign'.wf
        have hopened := hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
        rw [← Expr.instantiate1_eq] at hopened
        obtain ⟨fullBody, hfullBody', _⟩ := Hdom.body Hc hfullBody
        have hopenedFull := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType hfullBody'
        have hspineBody : ∃ n, Expr.ForallSpine body n := by
          cases Hspine with
          | codomain hh => cases hh
          | step hb => exact ⟨_, hb⟩
        obtain ⟨n, hn⟩ := hspineBody
        have hn' := hn.instantiateFVar (fv := ⟨c.ngen.curr⟩) (d := 0)
        rw [← Expr.instantiate1_eq] at hn'
        obtain ⟨htail, hrequired⟩ := ih Hnext Hruntime' halign' hn' hopened
          (hopenedFull.trExpr Hnext.checking.tr.wf Hnext.mlctx_wf.tr.wf)
        refine ⟨.field hdomType ?_ htail, ?_⟩
        · have hconsumed₀ := Hdom₀.proof_of_largeEliminationCheck
            (Hc := Hc.atCheckLCtx) Hdom₀ hcheck hzero
          obtain ⟨u, hu⟩ := Hdom₀.source_defeq
          have hsource₀ := hconsumed₀.defeqU_l Hc.checking.tr.wf
            Hc.check.wf.tr.wf.toCtx ⟨_, hu.symm⟩
          exact .inr (.inl (VEnv.HasType.alignBack Hc.checking.tr.wf halign
            hdomNarrow Hdom₀.source hsource₀))
        · intro fv hfv index type hfind
          apply ResultBVar.under
          have hfvMem : fv ∈ scope.fvars := VLCtx.find?_eq_some.mp ⟨_, hfind⟩
          have hne : fv ≠ ⟨c.ngen.curr⟩ := by
            have hfresh := hscopeWF.fvars_nodup
            simp only [VLCtx.fvars, List.filterMap_cons, Option.map_some, List.nodup_cons] at hfresh
            intro heq
            exact hfresh.1 (heq ▸ hfvMem)
          have hfind' := VLCtx.find?_vlam_ne
            (deps := (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList) (ty := narrowDom)
            (by simpa using hne.symm) hfind
          apply hrequired fv hfv (index + 1) _
          simpa [VExpr.lift, VExpr.liftN] using hfind'

  | @index c name dom body bi i required result hfield hcheck hzero Htail ih =>
    cases hnarrow with
    | @forallE narrowDom narrowBody _ _ _ _ _ hdomType hbodyType hdomNarrow hbodyNarrow =>
      obtain ⟨fullForall, hfullForall, _⟩ := hfull
      cases hfullForall with
      | forallE hfullDomType _ hfullDom hfullBody =>
        obtain ⟨consumed, Hdom⟩ := consumeTypeAnnotationsCompat c Hc hfullDom hfullDomType
        rcases halign.forallE_align Hc.checking.tr.wf hdomNarrow hdomType hbodyNarrow with
          ⟨dom₀, _, hdom₀, hdom₀Type, _, _, _⟩
        obtain ⟨consumed₀, Hdom₀⟩ :=
          consumeTypeAnnotationsCompat _ Hc.atCheckLCtx hdom₀ hdom₀Type
        let Hnext := Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
        have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
        obtain ⟨domainLevel, hdomain⟩ := Hruntime.unannotatedDomain Hc Hdom hdomNarrow
        let Hruntime' := Hruntime.withIndex Hnext.mlctx_wf.tr.wf hdeps name bi dom hdomNarrow hdomain hdomType
        have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
          Hdom Hdom₀ hdomNarrow hdomType hdeps
        have hscopeWF := halign'.wf
        have hopened := hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
        rw [← Expr.instantiate1_eq] at hopened
        obtain ⟨fullBody, hfullBody', _⟩ := Hdom.body Hc hfullBody
        have hopenedFull := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType hfullBody'
        have hspineBody : ∃ n, Expr.ForallSpine body n := by
          cases Hspine with
          | codomain hh => cases hh
          | step hb => exact ⟨_, hb⟩
        obtain ⟨n, hn⟩ := hspineBody
        have hn' := hn.instantiateFVar (fv := ⟨c.ngen.curr⟩) (d := 0)
        rw [← Expr.instantiate1_eq] at hn'
        obtain ⟨htail, hrequired⟩ := ih Hnext Hruntime' halign' hn' hopened
          (hopenedFull.trExpr Hnext.checking.tr.wf Hnext.mlctx_wf.tr.wf)
        refine ⟨.field hdomType ?_ htail, ?_⟩
        · apply Or.inr; apply Or.inr
          exact hrequired ⟨c.ngen.curr⟩ (by simp) 0 _ VLCtx.find?_vlam_self
        · intro fv hfv index type hfind
          apply ResultBVar.under
          have hfvMem : fv ∈ scope.fvars := VLCtx.find?_eq_some.mp ⟨_, hfind⟩
          have hne : fv ≠ ⟨c.ngen.curr⟩ := by
            have hfresh := hscopeWF.fvars_nodup
            simp only [VLCtx.fvars, List.filterMap_cons, Option.map_some, List.nodup_cons] at hfresh
            intro heq
            exact hfresh.1 (heq ▸ hfvMem)
          have hfind' := VLCtx.find?_vlam_ne
            (deps := (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList) (ty := narrowDom)
            (by simpa using hne.symm) hfind
          apply hrequired fv (by simp [hfv]) (index + 1) _
          simpa [VExpr.lift, VExpr.liftN] using hfind'

/-- Interpret the full closed constructor directly in the actual checker
context; ambient mutual-header locals cannot affect its literal arguments. -/
theorem LargeEliminationCheck.singletonClosed
    (H : LargeEliminationCheck stats c source 0 #[])
    (Hc : ContextWF c) (hchk : Hc.chk.vlctx = [])
    (Hspine : Expr.ForallSpine source arity)
    (Hsource : TrExprS Hc.venv c.lparams [] source target) :
    SingletonTelescope Hc.venv c.lparams.length stats.params.size [] 0 target := by
  have Hfull := Hsource.weakFV Hc.checking.tr.wf.orderedStrong
    (VLCtx.FVLift.to_append [] Hc.mlctx.noBV) (by simpa using Hc.mlctx_wf.tr.wf)
  have Hfull' : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx source (target.liftN Hc.mlctx.vlctx.toCtx.length) := by simpa using Hfull
  exact (H.singletonTelescope Hc (.empty Hc) (by rw [hchk]; exact .nil)
    Hspine Hsource
    (Hfull'.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)).1


end VerifyInductive
end Lean4Lean
